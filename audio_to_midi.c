/**
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdio.h>
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/adc.h"
#include "hardware/timer.h"
#include "hardware/dma.h"
#include "hardware/irq.h"
#include "hardware/spi.h"
#include <math.h>
#include "string.h"
#include "hardware/timer.h"

#include "pico/binary_info.h"
#include "bsp/board.h"
#include "tusb.h"
//====================================fixed point def ==========================
// Macros for fixed-point arithmetic (faster than floating point)
typedef signed int fix15;
#define multfix15(a, b) ((fix15)((((signed long long)(a)) * ((signed long long)(b))) >> 15))
#define float2fix15(a) ((fix15)((a) * 32768.0))
#define fix2float15(a) ((float)(a) / 32768.0)
#define absfix15(a) abs(a)
#define int2fix15(a) ((fix15)(a << 15))
#define fix2int15(a) ((int)(a >> 15))
#define char2fix15(a) (fix15)(((fix15)(a)) << 15)
#define divfix(a, b) (fix15)((((signed long long)(a)) << 15) / (b))

// ==========================================
// === fixed point s1x14
// ==========================================
// s1.14 format
// == resolution 2^-14 = 6.1035e-5
// == dynamic range is +1.9999/-2.0
typedef signed short s1x14;
#define muls1x14(a, b) ((s1x14)((((int)(a)) * ((int)(b))) >> 14))
#define float_to_s1x14(a) ((s1x14)((a) * 16384.0)) // 2^14
#define s1x14_to_float(a) ((float)(a) / 16384.0)
#define abss1x14(a) abs(a)
#define divs1x14(a, b) ((s1x14)((((signed int)(a) << 14) / (b))))
// shift 12 bits into 13 bits so full scale ADC is about 0.25
#define adc_to_s1x14(a) ((s1x14)((a) << 1))

// ==========================================
// === fixed point s15x16
// ==========================================
// s15x16 fixed point macros ==
// == resolution 2^-16 = 1.5e-5
// == dynamic range is 32767/-32768
typedef signed int s15x16;
#define muls15x16(a, b) ((s15x16)((((signed long long)(a)) * ((signed long long)(b))) >> 16)) // multiply two fixed 16:16
#define float_to_s15x16(a) ((s15x16)((a) * 65536.0))                                          // 2^16
#define s15x16_to_float(a) ((float)(a) / 65536.0)
#define s15x16_to_int(a) ((int)((a) >> 16))
#define int_to_s15x16(a) ((s15x16)((a) << 16))
#define divs15x16(a, b) ((s15x16)((((signed long long)(a) << 16) / (b))))
#define abss15x16(a) abs(a)
// the weird shift is to move the sign bits correctly
#define s1x14_to_s15x16(a) ((s15x16)(a) << 2);

// ==============================DAC CODE =====================================
// ============================================================================
/** SPI configurations (GPIO number, NOT pin number)
    Additional connections:
    3.3v (pin 36) -> VCC on DAC
    GND (pin 3)  -> GND on DAC */
#define PIN_MISO 4 // GPIO 2 (pin 4) GPIO output for timing ISR
#define PIN_CS 5   // GPIO 5 (pin 7) Chip select
#define PIN_SCK 6  // GPIO 6 (pin 9) SCK/spi0_sclk
#define PIN_MOSI 7 // GPIO 7 (pin 10) MOSI/spi0_tx
#define LDAC 8     // not sure if i need this
#define LED 25     // GPIO 25 LED
#define SPI_PORT spi0
uint16_t DAC_data_1; // output value
uint16_t DAC_data_0; // output value
volatile uint16_t DAC_output_0;
volatile uint16_t DAC_output_1;

// DAC parameters (in DAC datasheet)
// A-channel and B-Channel, 1x, active
#define DAC_config_chan_A 0b0011000000000000
#define DAC_config_chan_B 0b1011000000000000
//==========================================================
// ARRAY CONFIG
#define adc_array_length 512
short adc_data[adc_array_length];
short adc_data_copy[adc_array_length];

// ===========================================
// DSP definitions
// ===========================================
//
// FFT setup
#define N_WAVE adc_array_length /* size of FFT 512 */
#define LOG2_N_WAVE 9           /* log2(N_WAVE) 0 */

s1x14 Sinewave[N_WAVE];       // a table of sines for the FFT
s1x14 window[N_WAVE];         // a table of window values for the FFT
s1x14 fr[N_WAVE], fi[N_WAVE]; // input data

// ==================================
// === Init FFT arrays
//====================================
void FFTinit(void)
{
  // one cycle sine table
  //  required for FFT
  for (int ii = 0; ii < N_WAVE; ii++)
  {
    // one cycle per window for FFT -- scall amp for number of bits
    Sinewave[ii] = float_to_s1x14(0.5 * sin(6.283 * ((float)ii) / N_WAVE));
    // Raised cos window
    window[ii] = float_to_s1x14(1.0 - cos(6.283 * ((float)ii) / (N_WAVE - 1)));
  }
}
// ==================================
// === FFT
//====================================
void FFTfix(s1x14 fr[], s1x14 fi[], int m)
{
  // Adapted from code by:
  // Tom Roberts 11/8/89 and Malcolm Slaney 12/15/94 malcolm@interval.com
  // fr[n],fi[n] are real,imaginary arrays, INPUT AND RESULT.
  // size of data = 2**m
  //  This routine does foward transform only

  int mr, nn, i, j, L, k, istep, n;
  s1x14 qr, qi, tr, ti, wr, wi;

  mr = 0;
  n = 1 << m; // number of points
  nn = n - 1;

  /* decimation in time - re-order data */
  for (m = 1; m <= nn; ++m)
  {
    L = n;
    do
      L >>= 1;
    while (mr + L > nn);
    mr = (mr & (L - 1)) + L;
    if (mr <= m)
      continue;
    tr = fr[m];
    fr[m] = fr[mr];
    fr[mr] = tr;
    ti = fi[m];     // for real inputs, don't need this
    fi[m] = fi[mr]; // for real inputs, don't need this
    fi[mr] = ti;    // for real inputs, don't need this
  }

  L = 1;
  k = LOG2_N_WAVE - 1;
  while (L < n)
  {
    istep = L << 1;
    for (m = 0; m < L; ++m)
    {
      j = m << k;
      wr = Sinewave[j + N_WAVE / 4];
      wi = -Sinewave[j];
      // wr >>= 1; //do need if scale table
      // wi >>= 1;

      for (i = m; i < n; i += istep)
      {
        j = i + L;
        tr = muls1x14(wr, fr[j]) - muls1x14(wi, fi[j]);
        ti = muls1x14(wr, fi[j]) + muls1x14(wi, fr[j]);
        qr = fr[i] >> 1;
        qi = fi[i] >> 1;
        fr[j] = qr - tr;
        fi[j] = qi - ti;
        fr[i] = qr + tr;
        fi[i] = qi + ti;
      }
    }
    --k;
    L = istep;
  }
}

//====================================
// === magnitude approx good to about +/-2%
// see https://en.wikipedia.org/wiki/Alpha_max_plus_beta_min_algorithm
#define min(a, b) (((a) < (b)) ? (a) : (b))
#define max(a, b) (((a) > (b)) ? (a) : (b))
//====================================
void magnitude(s1x14 fr[], s1x14 fi[], int length)
{
  s1x14 mmax, mmin;
  s1x14 c1 = float_to_s1x14(0.89820);
  s1x14 c2 = float_to_s1x14(0.48597);
  for (int ii = 0; ii < length; ii++)
  {
    mmin = min(abs(fr[ii]), abs(fi[ii])); //>>9
    mmax = max(abs(fr[ii]), abs(fi[ii]));
    // reuse fr to hold magnitude
    fr[ii] = max(mmax, (muls1x14(mmax, c1) + muls1x14(mmin, c2)));
    fi[ii] = 0;
  }
}
//====================================
// log2 approx
// see:
// Generation of Products and Quotients Using Approximate Binary Logarithms
// for Digital Filtering Applications,
// IEEE Transactions on Computers 1970 vol.19 Issue No.02
//====================================
void log2_approx0(s1x14 fr[], int length)
{
  s15x16 log_input, log_output;
  // reduced range variable for interpolation
  s15x16 x;
  // low cutoff
  s15x16 low_cutoff = float_to_s15x16(0.00006);
  s15x16 c1 = float_to_s15x16(0.984);
  s15x16 c2 = float_to_s15x16(0.065);

  for (int ii = 0; ii < length; ii++)
  {
    log_input = s1x14_to_s15x16(fr[ii]);
    //
    // check for too small or negative
    // and return smallest log2
    if (log_input <= low_cutoff)
    {
      fr[ii] = -15;
      continue;
    }
    // if the input is less than 2 the scale up by
    // 2^14 so always working on an integer
    // so we can get logs down to input of 0.00003 or so approx -14.85
    int frac_factor = 0;
    if (log_input < int_to_s15x16(2))
    {
      // max size of shift to not overflow
      frac_factor = 14;
      log_input <<= frac_factor;
    }

    // temp for finding msb
    s15x16 sx;
    sx = log_input;

    // find the most-significant bit
    // equivalent to finding the characteristic of the log
    s15x16 y = 1;  // value of MSB
    s15x16 ly = 0; // position of MSB
    while (sx > int_to_s15x16(2))
    {
      y = y << 1;
      ly = ly + int_to_s15x16(1);
      sx = sx >> 1;
    }
    // bound the bottom and detect negative input values
    // Two-segment approx is good to better than  0.02 log unit
    // equiv to finding the mantissa of the log, then adding the charastic
    // see:
    // Generation of Products and Quotients Using Approximate Binary Logarithms
    // for Digital Filtering Applications,
    // IEEE Transactions on Computers 1970 vol.19 Issue No.02
    // normalize the bits after dleting MSB
    x = (log_input - y) >> (int)ly;
    // piecewise linear curve fit
    // if(x<0.5) log_output = (ly + x*1.163 + 0.0213) - frac_factor ;
    // else      log_output = (ly + x*0.828 + 0.1815) - frac_factor ;
    // one segment approx goodd to about 0.07 log unit
    log_output = (ly + x * c1 + c2) - frac_factor;
    // and store it
    fr[ii] = log_output >> 16;
    //
  }
}

#define log_min 0x00
// reuse fr to hold log magnitude
// shifting finds most significant bit
// then make approxlog  = ly + (fr-y)./(y) + 0.043;
// BUT for an 8-bit approx (4 bit ly and 4-bit fraction)
// ly 1<=ly<=14
// omit the 0.043 because it is too small for 4-bit fraction
void log2_approx(s1x14 fr[], int length)
{
  //
  int sx, y, ly, temp;
  for (int i = 0; i < length; i++)
  {
    // interpret bits as integer
    sx = fr[i];
    y = 1;
    ly = 0;
    while (sx > 1)
    {
      y = y * 2;
      ly = ly + 1;
      sx = sx >> 1;
    }
    // shift ly into upper 4-bits as integer part of log
    // take bits below y and shift into lower 4-bits
    // !!NOTE that fr is no longer in s1x14 format!!
    fr[i] = ((ly) << 4) + ((fr[i] - y) >> (ly - 4));
    // bound the noise at low amp
    if (fr[i] < log_min)
      fr[i] = log_min;
  }
}

// ================FFT PROCESSING===============================================
// =============================================================================

// TODO: Accurately calculate bin conversion factor - get better conversion rate
// s15x16 binConversion = float_to_s15x16(86.1328); // 441000/512.0;
// s15x16 binConversion = float_to_s15x16(31.25); // 16000/512.0;
s15x16 binConversion = float_to_s15x16(9.76); //

// s15x16 binConversion = float_to_s15x16(15.63); // 16000/1024.0;

s15x16 two = float2fix15(2.0);
float freq_float = 0.0;
void compute_fft()
{
  for (int i = 0; i < N_WAVE; i++)
  {
    fr[i] = adc_to_s1x14(adc_data_copy[i]); // adc_to_s1x14
  }
  // do the windowing
  for (int i = 0; i < N_WAVE; i++)
  {
    fr[i] = muls1x14(fr[i], window[i]);
    fi[i] = 0;
  }

  // do the FFT
  FFTfix(fr, fi, LOG2_N_WAVE);
  //
  // compute power spectrum
  magnitude(fr, fi, N_WAVE);

  // find max of magnitude for freq estimate - then convert
  s1x14 max_mag = 0;
  int max_mag_index = 0;
  for (int i = 2; i < adc_array_length / 2; i++)
  {
    //
    if (fr[i] > max_mag)
    {
      max_mag = fr[i];
      max_mag_index = i;
    }
  }

  s15x16 binIndex = int_to_s15x16(max_mag_index);                   // convert bin to fix 15
  s15x16 freq = divs15x16(muls15x16(binIndex, binConversion), two); // convert bin to frequency
  freq_float = s15x16_to_float(freq);                               // div by 2
}

// todo: sample rate test
//================================ADC DMA DAC CONFIG============================
//==============================================================================
int adc_init_helper(int dma_timer)
{
  adc_init();
  adc_gpio_init(26);   // GPIO 26, pin 31
  adc_select_input(0); // ADC input 0 (GPIO26)

  // 48 MHz clock / 44.1 KHz sample rate -> 1088
  // now 16khz = 48MHz
  adc_set_clkdiv(9600);
  adc_run(1); // set free run
  // fifo_enable, dreq_enable, thresh=1, no error, dont shift to 8-bits(for 8-bit PWM)
  adc_fifo_setup(1, 1, 1, 0, 0);

  // DMA config
  int ADC_data_chan = dma_claim_unused_channel(true);
  dma_channel_config c2 = dma_channel_get_default_config(ADC_data_chan);
  channel_config_set_transfer_data_size(&c2, DMA_SIZE_16);
  channel_config_set_read_increment(&c2, false); // reading from ADC fifo
  channel_config_set_write_increment(&c2, true); // write increments
  channel_config_set_irq_quiet(&c2, true);       // turn off interrupt handler
  channel_config_set_enable(&c2, true);          // enable channel
  channel_config_set_dreq(&c2, DREQ_ADC);        // adc gets a new sample (adc is on a timer)

  dma_channel_configure(ADC_data_chan, &c2,
                        adc_data,         // write_addr, array
                        &adc_hw->fifo,    // read_addr, fifo
                        adc_array_length, // ADC array size,
                        0);               // trigger
  return ADC_data_chan;
}

// Initialize DAC and corresponding DMA channel
int dac_init_helper(int dma_timer)
{
  // Initialize SPI channel (channel, baud rate set to 20MHz)
  spi_init(SPI_PORT, 20000000);
  // Format (channel, data bits per transfer, polarity, phase, order)
  spi_set_format(SPI_PORT, 16, 0, 0, 0);
  // Map SPI signals to GPIO ports
  gpio_set_function(PIN_MISO, GPIO_FUNC_SPI);
  gpio_set_function(PIN_SCK, GPIO_FUNC_SPI);
  gpio_set_function(PIN_MOSI, GPIO_FUNC_SPI);
  gpio_set_function(PIN_CS, GPIO_FUNC_SPI);

  // =======DMA config=====adapted from professor hunter adams code:=========
  // https://vanhunteradams.com/Pico/DAC/DMA_DAC.html

  int DAC_data_chan = dma_claim_unused_channel(true);
  dma_channel_config c2 = dma_channel_get_default_config(DAC_data_chan); // Default configs

  channel_config_set_transfer_data_size(&c2, DMA_SIZE_16); // 16-bit txfers
  channel_config_set_read_increment(&c2, true);            // yes read incrementing
  channel_config_set_write_increment(&c2, false);          // no write incrementing
  channel_config_set_irq_quiet(&c2, true);                 // turn off interrupt handler

  // DREQ paced by claimed dma timer
  channel_config_set_dreq(&c2, DREQ_ADC);

  dma_channel_configure(
      DAC_data_chan,             // Channel to be configured
      &c2,                       // The configuration we just created
      &spi_get_hw(SPI_PORT)->dr, // write address (SPI data register)
      &adc_data_copy[0],         // The initial read address
      adc_array_length,          // Number of transfers
      false                      // Don't start immediately.
  );
  return DAC_data_chan;
}

// =======DAC SPI CONVERSION before outputting=========
void convert_to_dac_array()
{
  for (size_t i = 0; i < adc_array_length; i++)
  {
    adc_data_copy[i] = DAC_config_chan_B | (adc_data_copy[i] & 0x0fff);
  }
}

//===========MIDI and usb code=========================================
//===================================================================
// frequency to midi number conversion
// TODO: Use fix 15
int freq_to_midi(float freq)
{
  // return (int)(69 + 12 * log2(freq / 440.0));
  return (int)(57.01 + (12 * log(freq / 220.0)) / log(2));
}

#define freq_array_length 9          // Number of frequencies to calculate median from
float freq_array[freq_array_length]; // Array to hold frequencies for median calculation

int comp(const void *a, const void *b)
{
  return (*(int *)a - *(int *)b);
}
// Calculate the median frequency from an array of ~7 frequencies
float get_median_freq(float freq_array[])
{
  qsort(freq_array, freq_array_length, sizeof(float), (int (*)(const void *, const void *))comp);
  printf("Median freq: %f\n", freq_array[freq_array_length / 2]);
  return freq_array[freq_array_length / 2]; // Return the middle element
}

enum
{
  BLINK_NOT_MOUNTED = 250,
  BLINK_MOUNTED = 1000,
  BLINK_SUSPENDED = 2500,
};

static uint32_t blink_interval_ms = BLINK_NOT_MOUNTED;
const uint LED_PIN = PICO_DEFAULT_LED_PIN;

void led_blinking_task(void);
void midi_task(void);

//--------------------------------------------------------------------+
// Device callbacks
//--------------------------------------------------------------------+

// Invoked when device is mounted
void tud_mount_cb(void)
{
  blink_interval_ms = BLINK_MOUNTED;
}

// Invoked when device is unmounted
void tud_umount_cb(void)
{
  blink_interval_ms = BLINK_NOT_MOUNTED;
}

// Invoked when usb bus is suspended
// remote_wakeup_en : if host allow us  to perform remote wakeup
// Within 7ms, device must draw an average of current less than 2.5 mA from bus
void tud_suspend_cb(bool remote_wakeup_en)
{
  (void)remote_wakeup_en;
  blink_interval_ms = BLINK_SUSPENDED;
}

// Invoked when usb bus is resumed
void tud_resume_cb(void)
{
  blink_interval_ms = BLINK_MOUNTED;
}

//--------------------------------------------------------------------+
// MIDI Task
//--------------------------------------------------------------------+

// Variable that holds the current position in the sequence.
uint32_t note_pos = 0;

// Store example melody as an array of note values
uint8_t note_sequence[] =
    {
        74, 78, 81, 86, 90, 93, 98, 102, 57, 61, 66, 69, 73, 78, 81, 85, 88, 92, 97, 100, 97, 92, 88, 85, 81, 78,
        74, 69, 66, 62, 57, 62, 66, 69, 74, 78, 81, 86, 90, 93, 97, 102, 97, 93, 90, 85, 81, 78, 73, 68, 64, 61,
        56, 61, 64, 68, 74, 78, 81, 86, 90, 93, 98, 102};

int prev_note = 0;
uint8_t msg[3];
void midi_play_note(int curr_note)
{
  // Send Note On for current position at full velocity (127) on channel 1.

  // play new note
  if (curr_note != prev_note && curr_note > 27 && curr_note < 128)

  // printf("Note: %d\n", curr_note);
  // printf("Prev Note: %d\n", prev_note);
  // printf("Msg: %d %d %d\n", msg[0], msg[1], msg[2]);
  {
    // printf("Note: %d\n", curr_note);

    // Send Note Off for previous note.
    msg[0] = 0x80;      // Note Off - Channel 1
    msg[1] = prev_note; // Note Number
    msg[2] = 0;         // Velocity
    tud_midi_n_stream_write(0, 0, msg, 3);

    // turn on new note
    msg[0] = 0x90;      // Note On - Channel 1
    msg[1] = curr_note; // Note Number
    msg[2] = 127;       // Velocity
    tud_midi_n_stream_write(0, 0, msg, 3);
    prev_note = curr_note;
  }
}

//--------------------------------------------------------------------+
// BLINKING TASK
//--------------------------------------------------------------------+
void led_blinking_task(void)
{
  static uint32_t start_ms = 0;
  static bool led_state = false;

  // Blink every interval ms
  if (board_millis() - start_ms < blink_interval_ms)
    return; // not enough time
  start_ms += blink_interval_ms;

  board_led_write(led_state);
  led_state = 1 - led_state; // toggle
}

//========================================================

int freq_array_index = 0; // Index for storing frequencies in freq_array
// =============================MAIN LOOP=======================================
int main()
{
  // Inits, USB, ADC, DMA, DAC config
  stdio_init_all();
  board_init();
  tusb_init();
  FFTinit();

  // (X/Y)*sys_clk, where X is the first 16 bytes and Y is the second
  // sys_clk is 125 MHz unless changed in code. Configured to ~44 kHz
  int dma_timer = dma_claim_unused_timer(true);
  dma_timer_set_fraction(dma_timer, 0x0017, 0xffff);
  int ADC_data_chan = adc_init_helper(dma_timer);
  int DAC_data_chan = dac_init_helper(dma_timer); // dont need right now

  dma_start_channel_mask(1u << ADC_data_chan); // start input data transfer
  while (1)
  {
    tud_task(); // tinyusb device task
    // led_blinking_task(); // get rid of it

    // Check if ADC buffer transfer complete, copy to processing array
    if (!dma_channel_is_busy(ADC_data_chan))
    {
      // copy data and wrap buffer around
      memcpy(adc_data_copy, adc_data, adc_array_length * 2); // dont need to copy for now
      dma_channel_set_write_addr(ADC_data_chan, adc_data, 1);

      // ==================AUDIO PROCESSING BLOCK========================
      compute_fft();
      freq_array[freq_array_index] = freq_float;                     // Store the frequency in the array
      freq_array_index = (freq_array_index + 1) % freq_array_length; // Increment index and wrap around

      // ==================AUDIO OUTPUT BLOCK========================
      // convert_to_dac_array();                                     // add DAC bits
      // dma_channel_set_read_addr(DAC_data_chan, adc_data_copy, 1); // wrap around

      // ==============MIDI OUTPUT BLOCK=================================
      if (freq_array_index == 0)
      {
        int midi_note = freq_to_midi(get_median_freq(freq_array)); // TODO: use fix 15
        midi_play_note(midi_note);
      }
    }
  }
}