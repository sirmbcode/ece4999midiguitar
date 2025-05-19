void midi_task(void)
{
  static uint32_t start_ms = 0;
  uint8_t msg[3];

  // send note every 1000 ms
  if (board_millis() - start_ms < 286)
    return; // not enough time
  start_ms += 286;

  // Previous positions in the note sequence.
  int previous = note_pos - 1;

  // If we currently are at position 0, set the
  // previous position to the last note in the sequence.
  if (previous < 0)
    previous = sizeof(note_sequence) - 1;

  // Send Note On for current position at full velocity (127) on channel 1.
  msg[0] = 0x90;                    // Note On - Channel 1
  msg[1] = note_sequence[note_pos]; // Note Number
  msg[2] = 127;                     // Velocity
  tud_midi_n_stream_write(0, 0, msg, 3);

  // Send Note Off for previous note.
  msg[0] = 0x80;                    // Note Off - Channel 1
  msg[1] = note_sequence[previous]; // Note Number
  msg[2] = 0;                       // Velocity
  tud_midi_n_stream_write(0, 0, msg, 3);

  // Increment position
  note_pos++;

  // If we are at the end of the sequence, start over.
  if (note_pos >= sizeof(note_sequence))
    note_pos = 0;
}