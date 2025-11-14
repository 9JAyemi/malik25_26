// SVA for tlu_prencoder16
// Bind with a free-running clock: bind tlu_prencoder16 tlu_prencoder16_sva u_sva (.*,.clk(tb_clk));

module tlu_prencoder16_sva (
  input logic                   clk,
  input logic [15:0]            din,
  input logic [3:0]             dout,
  input logic [15:0]            onehot
);

  default clocking cb @(posedge clk); endclocking

  // Structural sanity
  a_onehot0: assert property ($onehot0(onehot));

  // Zero input -> zero outputs
  a_zero_case: assert property ((din == 16'b0) |-> (onehot == 16'b0 && dout == 4'd0));

  // X-propagation: known inputs imply known outputs
  a_no_x_out: assert property ((!$isunknown(din)) |-> (!$isunknown({onehot,dout})));

  // When a onehot bit is selected, dout must equal its index
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : GEN_OH_TO_CODE
      a_oh_enc: assert property (onehot[i] |-> (dout == 4'(i)));
    end
  endgenerate

  // Priority function: first (lowest index) 1 in din determines dout
  // i=0: din[0] alone implies code 0
  a_prio0: assert property (din[0] |-> (dout == 4'd0));
  // i>0: din[i] with no lower 1s implies code i
  generate
    for (i = 1; i < 16; i++) begin : GEN_PRIO
      a_prio_i: assert property ((din[i] && ~(|din[i-1:0]))) |-> (dout == 4'(i));
    end
  endgenerate

  // Coverage: hit each selected index and the zero case
  cover_zero: cover property (din == 16'b0);
  generate
    for (i = 0; i < 16; i++) begin : GEN_COV
      c_oh_i:    cover property (onehot[i]);
      c_prio_i:  cover property ((i==0) ? din[0]
                                        : (din[i] && ~(|din[i-1:0])) );
    end
  endgenerate

endmodule