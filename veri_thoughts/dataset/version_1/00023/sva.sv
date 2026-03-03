// SVA checker for BCD_Converter
// Bind this to the DUT; provide a clock/reset from your TB.
module bcd_converter_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  bin,
  input  logic [3:0]  bcd
);

  // Golden model (derived from the DUT's logic)
  function automatic logic [3:0] exp_bcd (input logic [3:0] b);
    unique case (b)
      4'h0: exp_bcd = 4'h0;
      4'h1: exp_bcd = 4'h1;
      4'h2: exp_bcd = 4'h0;
      4'h3: exp_bcd = 4'h2;
      4'h4: exp_bcd = 4'h0;
      4'h5: exp_bcd = 4'h0;
      4'h6: exp_bcd = 4'h2;
      4'h7: exp_bcd = 4'h4;
      4'h8: exp_bcd = 4'h1;
      4'h9: exp_bcd = 4'h2;
      4'hA: exp_bcd = 4'h1;
      4'hB: exp_bcd = 4'h4;
      4'hC: exp_bcd = 4'h3;
      4'hD: exp_bcd = 4'h4;
      4'hE: exp_bcd = 4'h4;
      4'hF: exp_bcd = 4'h8;
      default: exp_bcd = 'x;
    endcase
  endfunction

  // Inputs must be known when sampled
  a_inputs_known: assert property (@(posedge clk) disable iff (!rst_n)
                                   !$isunknown(bin));

  // Functional equivalence to golden model
  a_functional:   assert property (@(posedge clk) disable iff (!rst_n)
                                   !$isunknown(bin) |-> (bcd === exp_bcd(bin)));

  // Output domain sanity (only values the DUT can produce)
  a_out_domain:   assert property (@(posedge clk) disable iff (!rst_n)
                                   !$isunknown(bin) |-> (bcd inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h8}));

  // Stable output if input is stable across cycles
  a_stability:    assert property (@(posedge clk) disable iff (!rst_n)
                                   (bin == $past(bin)) |-> (bcd == $past(bcd)));

  // Coverage: hit every input and its expected output
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV_IN_OUT
      c_in_out: cover property (@(posedge clk) disable iff (!rst_n)
                                (bin == i[3:0]) && (bcd == exp_bcd(i[3:0])));
    end
  endgenerate

  // Coverage: each output bit toggles both ways
  genvar j;
  generate
    for (j = 0; j < 4; j++) begin : COV_TOGGLE
      c_rose: cover property (@(posedge clk) disable iff (!rst_n) $rose(bcd[j]));
      c_fell: cover property (@(posedge clk) disable iff (!rst_n) $fell(bcd[j]));
    end
  endgenerate

endmodule

// Example bind (adjust clk/rst_n to your environment)
// bind BCD_Converter bcd_converter_sva u_bcd_converter_sva (.clk(clk), .rst_n(rst_n), .bin(bin), .bcd(bcd));