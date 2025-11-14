// SVA checkers for the provided design.
// Hook these up via bind statements and connect a sampling clock from your TB.

module top_module_sva (input logic clk);
  // This checker is bound into top_module and can see its internal nets.
  default clocking cb @(posedge clk); endclocking

  // Arithmetic/conn checks
  a_add_sum:        assert property (binary_sum == ({1'b0, ABC} + 4'd1)[3:0]);
  a_dec_in_conn:    assert property (decoder_input == binary_sum[2:0]);

  // Spec-level intent: top Y should match decoder_output
  a_y_matches_dec:  assert property (Y == decoder_output);

  // No X/Z on outputs when inputs are known
  a_known:          assert property (!$isunknown({ABC,EN}) |-> !$isunknown({binary_sum,decoder_input,decoder_output,Y}));

  // Basic functional coverage
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_abc_cov
      c_abc: cover property (ABC == i[2:0]);
    end
  endgenerate
  c_en0: cover property (EN == 1'b0);
  c_en1: cover property (EN == 1'b1);
  c_y_eq_dec: cover property (Y == decoder_output);
endmodule

module decoder_sva (input logic clk);
  // Function-table correctness for decoder
  default clocking cb @(posedge clk); endclocking

  ap_0001: assert property ( ({ABC,EN}==4'b0001) |-> (Y==8'b11000000) );
  ap_0010: assert property ( ({ABC,EN}==4'b0010) |-> (Y==8'b11111001) );
  ap_0011: assert property ( ({ABC,EN}==4'b0011) |-> (Y==8'b10100100) );
  ap_0100: assert property ( ({ABC,EN}==4'b0100) |-> (Y==8'b10110000) );
  ap_0101: assert property ( ({ABC,EN}==4'b0101) |-> (Y==8'b10011001) );
  ap_0110: assert property ( ({ABC,EN}==4'b0110) |-> (Y==8'b10010010) );
  ap_0111: assert property ( ({ABC,EN}==4'b0111) |-> (Y==8'b10000010) );
  ap_1000: assert property ( ({ABC,EN}==4'b1000) |-> (Y==8'b11111000) );

  ap_default: assert property ( !(({ABC,EN} inside {4'b0001,4'b0010,4'b0011,4'b0100,4'b0101,4'b0110,4'b0111,4'b1000})) |-> (Y==8'b00000000) );

  // Known output when inputs known
  ap_known: assert property (!$isunknown({ABC,EN}) |-> !$isunknown(Y));

  // Coverage of all table entries (plus default)
  cp_0001: cover property ({ABC,EN}==4'b0001);
  cp_0010: cover property ({ABC,EN}==4'b0010);
  cp_0011: cover property ({ABC,EN}==4'b0011);
  cp_0100: cover property ({ABC,EN}==4'b0100);
  cp_0101: cover property ({ABC,EN}==4'b0101);
  cp_0110: cover property ({ABC,EN}==4'b0110);
  cp_0111: cover property ({ABC,EN}==4'b0111);
  cp_1000: cover property ({ABC,EN}==4'b1000);
  cp_default: cover property (!({ABC,EN} inside {4'b0001,4'b0010,4'b0011,4'b0100,4'b0101,4'b0110,4'b0111,4'b1000}));
endmodule

module binary_adder_sva (input logic clk);
  // Pure combinational adder correctness (lower 4 bits of sum)
  default clocking cb @(posedge clk); endclocking
  ap_sum: assert property ( S == ({1'b0, X} + {1'b0, Y})[3:0] );

  // Known output when inputs known
  ap_known: assert property (!$isunknown({X,Y}) |-> !$isunknown(S));
endmodule

// Example bind statements (edit clock hookup to your TB clock)
// bind top_module     top_module_sva     u_top_sva     (.clk(<your_clk>));
// bind decoder        decoder_sva        u_decoder_sva (.clk(<your_clk>));
// bind binary_adder   binary_adder_sva   u_adder_sva   (.clk(<your_clk>));