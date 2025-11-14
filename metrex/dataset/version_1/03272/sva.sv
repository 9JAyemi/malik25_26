// SVA for crc_module
// Focus: correctness of sequential behavior, latency, X checks, and branch coverage.
// Bind into the DUT type so internals (crc_reg, data_reg, i) are visible.

bind crc_module crc_module_sva u_crc_module_sva (.*);

module crc_module_sva #(parameter POLY = 16'hA001)
(
  input logic        clk,
  input logic [31:0] data_in,
  input logic [15:0] crc_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // One-step CRC transform as implemented by the DUT (last NB-assignment wins)
  function automatic [15:0] step(input [15:0] c);
    automatic logic [15:0] rot;
    rot  = {c[14:0], c[15]};          // rotate MSB into LSB
    step = c[15] ? (rot ^ POLY) : rot;
  endfunction

  // Sanity/X checks (after init)
  a_no_x:           assert property ( !$isunknown({crc_out, crc_reg, data_reg}) );

  // Pipeline/latency checks
  a_data_reg_lat:   assert property ( data_reg == $past(data_in) );
  a_crc_out_lat:    assert property ( crc_out  == $past(crc_reg) );

  // Functional step check (NB assignment ordering reduces the 32-iter loop to a single step)
  a_crc_step:       assert property ( crc_reg == step($past(crc_reg)) );

  // Optional elaboration-time guard on loop index width (non-SVA but highly recommended)
  initial begin
    if ($bits(i) < 6) $error("crc_module: loop index i width (%0d) insufficient for 0..31", $bits(i));
  end

  // Coverage
  c_msb0:           cover property ( !$past(crc_reg[15]) );
  c_msb1:           cover property (  $past(crc_reg[15]) );
  c_data_activity:  cover property (  $changed(data_in) );
  c_branch_xor:     cover property (  $past(crc_reg[15]) &&
                                     crc_reg == ({$past(crc_reg[14:0]), $past(crc_reg[15])} ^ POLY) );
  c_branch_noxor:   cover property ( !$past(crc_reg[15]) &&
                                     crc_reg ==  ({$past(crc_reg[14:0]), $past(crc_reg[15])}) );
endmodule