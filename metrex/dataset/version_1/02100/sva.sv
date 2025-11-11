// SVA checkers and binds for the provided DUT (concise, quality-focused)

// parity_bit checker: validates internal equations, X-checks, and basic coverage
module parity_bit_sva;
  default clocking cb @(posedge $global_clock); endclocking

  // X checks
  a_nox_in:  assert property (!$isunknown(in));
  a_nox_out: assert property (!$isunknown({and_out, xor_out, parity}));

  // Functional invariants (purely combinational, hold every cycle)
  a_and: assert property (##0 and_out == (in[7:4] & in[3:0]));
  a_xor: assert property (##0 xor_out == (^in));
  a_par: assert property (##0 parity == (&and_out) & xor_out);

  // Minimal but meaningful coverage
  c_par0:   cover property (parity == 1'b0);
  c_par1:   cover property (parity == 1'b1);
  c_all0:   cover property (in == 8'h00);
  c_all1:   cover property (in == 8'hFF);
  c_onehot: cover property ($onehot(in));
endmodule

bind parity_bit parity_bit_sva;


// combinational_logic checker: bit-wise functional equivalence, X-checks, and bit coverage
module combinational_logic_sva;
  default clocking cb @(posedge $global_clock); endclocking

  a_nox_in:  assert property (!$isunknown(in));
  a_nox_out: assert property (!$isunknown(out_logic));

  a_b0: assert property (##0 out_logic[0] == (in[0] & in[1]));
  a_b1: assert property (##0 out_logic[1] == (in[1] | in[2]));
  a_b2: assert property (##0 out_logic[2] == (in[2] ^ in[3]));
  a_b3: assert property (##0 out_logic[3] == (in[0] & in[3]));

  // Coverage: each output bit can be 0 and 1 at some time
  c_b0_0: cover property (out_logic[0] == 1'b0);
  c_b0_1: cover property (out_logic[0] == 1'b1);
  c_b1_0: cover property (out_logic[1] == 1'b0);
  c_b1_1: cover property (out_logic[1] == 1'b1);
  c_b2_0: cover property (out_logic[2] == 1'b0);
  c_b2_1: cover property (out_logic[2] == 1'b1);
  c_b3_0: cover property (out_logic[3] == 1'b0);
  c_b3_1: cover property (out_logic[3] == 1'b1);
endmodule

bind combinational_logic combinational_logic_sva;


// sum_computation checker: arithmetic spec, X-checks, wrap coverage
module sum_computation_sva;
  default clocking cb @(posedge $global_clock); endclocking

  a_nox_in:  assert property (!$isunknown({parity, xor_out}));
  a_nox_out: assert property (!$isunknown(sum));

  // Functional relation: modulo 16 sum of 1-bit parity and 4-bit operand
  a_sum: assert property (##0 sum == ((parity + xor_out) % 16));

  // Coverage: no-wrap and wrap-around
  c_nowrap: cover property (parity == 1'b0 && xor_out == 4'h0 && sum == 4'h0);
  c_wrap:   cover property (parity == 1'b1 && xor_out == 4'hF && sum == 4'h0);
endmodule

bind sum_computation sum_computation_sva;


// Top-level integration checker: end-to-end golden equivalence + connectivity + coverage
module top_module_sva;
  default clocking cb @(posedge $global_clock); endclocking

  function automatic [3:0] f_logic(input logic [7:0] din);
    f_logic[0] = din[7] & din[6]; // mapping per top: {din[4],din[5],din[6],din[7]} -> [0]&[1]
    f_logic[1] = din[6] | din[5];
    f_logic[2] = din[5] ^ din[4];
    f_logic[3] = din[7] & din[4];
  endfunction

  function automatic logic f_parity(input logic [7:0] din);
    f_parity = (&(din[7:4] & din[3:0])) & (^din);
  endfunction

  // X checks
  a_nox_in:  assert property (!$isunknown(in));
  a_nox_out: assert property (!$isunknown(out_logic));

  // Connectivity: out_logic is driven by sum
  a_conn: assert property (##0 out_logic == sum);

  // End-to-end: out_logic equals golden composition from 'in'
  a_e2e: assert property (##0 out_logic == ((f_parity(in) + f_logic(in)) & 4'hF));

  // Integration coverage
  c_par0_path: cover property (f_parity(in) == 1'b0 && out_logic == f_logic(in));
  c_par1_wrap: cover property (f_parity(in) == 1'b1 && f_logic(in) == 4'hF && out_logic == 4'h0);
endmodule

bind top_module top_module_sva;