// SVA for key_encoder
module key_encoder_sva (
  input logic        clk,
  input logic [8:0]  key_input,
  input logic [4:0]  key_code,
  input logic [1:0]  range,
  input logic [2:0]  key_note
);
  default clocking cb @(posedge clk); endclocking

  // X-propagation guard: when inputs known, outputs must be known post-update
  a_no_x: assert property ( !$isunknown(key_input) |-> ##0 !$isunknown({range,key_note,key_code}) )
    else $error("key_encoder: X/Z detected on outputs with known inputs");

  // Domain checks (post-update)
  a_range_domain: assert property ( 1 |-> ##0 (range inside {[0:3]}) )
    else $error("key_encoder: range out of [0..3]");
  a_note_domain:  assert property ( 1 |-> ##0 (key_note inside {[0:7]}) )
    else $error("key_encoder: key_note out of [0..7]");

  // Range decode (key_input[8:7] -> range)
  a_rng_11: assert property ( (key_input[8:7]==2'b11) |-> ##0 (range==2'd0) )
    else $error("key_encoder: range decode mismatch for 2'b11");
  a_rng_01: assert property ( (key_input[8:7]==2'b01) |-> ##0 (range==2'd1) )
    else $error("key_encoder: range decode mismatch for 2'b01");
  a_rng_00: assert property ( (key_input[8:7]==2'b00) |-> ##0 (range==2'd2) )
    else $error("key_encoder: range decode mismatch for 2'b00");
  a_rng_10: assert property ( (key_input[8:7]==2'b10) |-> ##0 (range==2'd3) )
    else $error("key_encoder: range decode mismatch for 2'b10");

  // Note decode (key_input[6:0] -> key_note)
  a_note_1: assert property ( (key_input[6:0]==7'b0000001) |-> ##0 (key_note==3'd1) )
    else $error("key_encoder: note decode mismatch for 1");
  a_note_2: assert property ( (key_input[6:0]==7'b0000010) |-> ##0 (key_note==3'd2) )
    else $error("key_encoder: note decode mismatch for 2");
  a_note_3: assert property ( (key_input[6:0]==7'b0000100) |-> ##0 (key_note==3'd3) )
    else $error("key_encoder: note decode mismatch for 4");
  a_note_4: assert property ( (key_input[6:0]==7'b0001000) |-> ##0 (key_note==3'd4) )
    else $error("key_encoder: note decode mismatch for 8");
  a_note_5: assert property ( (key_input[6:0]==7'b0010000) |-> ##0 (key_note==3'd5) )
    else $error("key_encoder: note decode mismatch for 16");
  a_note_6: assert property ( (key_input[6:0]==7'b0100000) |-> ##0 (key_note==3'd6) )
    else $error("key_encoder: note decode mismatch for 32");
  a_note_7: assert property ( (key_input[6:0]==7'b1000000) |-> ##0 (key_note==3'd7) )
    else $error("key_encoder: note decode mismatch for 64");
  // Default path: any non-listed pattern (including zero or multi-bit) -> key_note==0
  a_note_def: assert property ( !(key_input[6:0] inside {
                                  7'b0000001,7'b0000010,7'b0000100,7'b0001000,
                                  7'b0010000,7'b0100000,7'b1000000})
                                |-> ##0 (key_note==3'd0) )
    else $error("key_encoder: default note decode mismatch");

  // Product check (combinational mapping)
  a_product: assert property ( 1 |-> ##0 (key_code == (range * key_note)) )
    else $error("key_encoder: key_code != range*key_note");

  // Functional coverage (concise but meaningful)
  // Cover each range value and each note value (incl. default 0), and a max product case
  c_range0: cover property ( 1 |-> ##0 (range==2'd0) );
  c_range1: cover property ( 1 |-> ##0 (range==2'd1) );
  c_range2: cover property ( 1 |-> ##0 (range==2'd2) );
  c_range3: cover property ( 1 |-> ##0 (range==2'd3) );

  c_note0: cover property ( 1 |-> ##0 (key_note==3'd0) );
  c_note1: cover property ( 1 |-> ##0 (key_note==3'd1) );
  c_note2: cover property ( 1 |-> ##0 (key_note==3'd2) );
  c_note3: cover property ( 1 |-> ##0 (key_note==3'd3) );
  c_note4: cover property ( 1 |-> ##0 (key_note==3'd4) );
  c_note5: cover property ( 1 |-> ##0 (key_note==3'd5) );
  c_note6: cover property ( 1 |-> ##0 (key_note==3'd6) );
  c_note7: cover property ( 1 |-> ##0 (key_note==3'd7) );

  // Cover default case due to multi-bit press and the max product (3*7=21)
  c_multi_bit_default: cover property ( ($countones(key_input[6:0])>1) |-> ##0 (key_note==3'd0) );
  c_product_max:       cover property ( 1 |-> ##0 (key_code==5'd21) );

endmodule

// Bind into DUT (connect to internal regs range/key_note)
bind key_encoder key_encoder_sva u_key_encoder_sva (
  .clk(clk),
  .key_input(key_input),
  .key_code(key_code),
  .range(range),
  .key_note(key_note)
);