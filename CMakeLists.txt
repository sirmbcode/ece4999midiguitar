# Generated Cmake Pico project file

cmake_minimum_required(VERSION 3.13)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Initialise pico_sdk from installed location
# (note this can come from environment, CMake cache etc)

# == DO NOT EDIT THE FOLLOWING LINES for the Raspberry Pi Pico VS Code Extension to work ==
if(WIN32)
    set(USERHOME $ENV{USERPROFILE})
else()
    set(USERHOME $ENV{HOME})
endif()
set(sdkVersion 2.1.0)
set(toolchainVersion 13_3_Rel1)
set(picotoolVersion 2.1.0)
set(picoVscode ${USERHOME}/.pico-sdk/cmake/pico-vscode.cmake)
if (EXISTS ${picoVscode})
    include(${picoVscode})
endif()
# ====================================================================================
set(PICO_BOARD pico CACHE STRING "Board type")

# Disable SDK alarm support for this lowlevel example
set(PICO_TIME_DEFAULT_ALARM_POOL_DISABLED 1)

# Pull in Raspberry Pi Pico SDK (must be before project)
include(pico_sdk_import.cmake)

project(audio_to_midi C CXX ASM)

# Initialise the Raspberry Pi Pico SDK
pico_sdk_init()

# Add executable. Default name is the project name, version 0.1

add_executable(audio_to_midi
audio_to_midi.c usb_descriptors.c
        )

# Modify the below lines to enable/disable output over UART/USB
pico_enable_stdio_uart(audio_to_midi 0)
pico_enable_stdio_usb(audio_to_midi 1)

target_include_directories(audio_to_midi PRIVATE ${CMAKE_CURRENT_LIST_DIR})


target_link_libraries(audio_to_midi pico_stdlib hardware_adc hardware_spi 
hardware_dma pico_bootsel_via_double_reset tinyusb_device tinyusb_board)
# create map/bin/hex file etc.
pico_add_extra_outputs(audio_to_midi)

# add url via pico_set_program_url
