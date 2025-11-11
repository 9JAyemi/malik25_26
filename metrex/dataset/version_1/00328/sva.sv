// SVA for crc_module and Test. Bind these modules to the DUTs.

////////////////////////////////////////////////////////////////////////////////
// crc_module SVA
////////////////////////////////////////////////////////////////////////////////
module crc_module_sva;
  // Access DUT scope via bind. Assumes signals exist in crc_module.
  default clocking cb @(posedge clk); endclocking

  // cyc must increment by 1 when previous value is known
  a_cyc_inc: assert property ( !$isunknown($past(cyc)) |-> cyc == $past(cyc)+1 );

  // Seed load takes effect when cyc==0 (overrides shift)
  a_seed_load: assert property ( (cyc==0) |=> crc == 64'h5aef0c8d_d70a4497 );

  // CRC next-state function when not loading seed
  a_crc_update: assert property ( (cyc!=0) |=> crc ==
                                  { $past(crc)[62:0],
                                    $past(crc)[63] ^ $past(crc)[2] ^ $past(crc)[0] } );

  // o wires must mirror crc bit pairs
  a_o0: assert property ( o[0] == {crc[1],crc[0]} );
  a_o1: assert property ( o[1] == {crc[3],crc[2]} );
  a_o2: assert property ( o[2] == {crc[5],crc[4]} );
  a_o3: assert property ( o[3] == {crc[7],crc[6]} );

  // Checksum update formatting when cyc>=90 (uses pre-state crc via NBA semantics)
  a_checksum_update: assert property (
    (cyc>=90) |=> checksum ==
      { 32'h0, 6'h0, {$past(crc)[7],$past(crc)[6]},
        6'h0, {$past(crc)[5],$past(crc)[4]},
        6'h0, {$past(crc)[3],$past(crc)[2]},
        6'h0, {$past(crc)[1],$past(crc)[0]} }
  );

  // No checksum write before 90
  a_checksum_hold_before_90: assert property ( (cyc<90) |=> $stable(checksum) );

  // CRC becomes known right after the seed load
  a_crc_known_post_seed: assert property ( (cyc==0) |=> !$isunknown(crc) );

  // Coverage
  c_seen_seed:     cover property (cyc==0);
  c_seen_ge_90:    cover property (cyc>=90);
  c_checksum_write: cover property (
    (cyc>=90) |=> checksum ==
      { 32'h0, 6'h0, {$past(crc)[7],$past(crc)[6]},
        6'h0, {$past(crc)[5],$past(crc)[4]},
        6'h0, {$past(crc)[3],$past(crc)[2]},
        6'h0, {$past(crc)[1],$past(crc)[0]} }
  );
endmodule

bind crc_module crc_module_sva crc_module_sva_i();


////////////////////////////////////////////////////////////////////////////////
// Test SVA (combinational truth table)
////////////////////////////////////////////////////////////////////////////////
module Test_sva;
  // Assertions for each input mapping (use 4-state equality to guard Xs)
  a_map_00: assert property (@(*)) (i===2'b00) |-> (o===2'b00);
  a_map_01: assert property (@(*)) (i===2'b01) |-> (o===2'b11);
  a_map_10: assert property (@(*)) (i===2'b10) |-> (o===2'b01);
  a_map_11: assert property (@(*)) (i===2'b11) |-> (o===2'b10);

  // Output must be known for all valid inputs
  a_no_x_when_valid_i: assert property (@(*))
    (i inside {2'b00,2'b01,2'b10,2'b11}) |-> !$isunknown(o);

  // Coverage of all mappings
  c_00: cover property (@(*)) i===2'b00 && o===2'b00;
  c_01: cover property (@(*)) i===2'b01 && o===2'b11;
  c_10: cover property (@(*)) i===2'b10 && o===2'b01;
  c_11: cover property (@(*)) i===2'b11 && o===2'b10;
endmodule

bind Test Test_sva Test_sva_i();