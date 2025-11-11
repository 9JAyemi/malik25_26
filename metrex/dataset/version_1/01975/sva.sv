// SVA checker for decoder. Binds into DUT and verifies latency, mapping, one-hotness, and internal captures.

module decoder_sva (
  input logic        clk,
  input logic [2:0]  ABC,
  input logic [7:0]  Y,
  input logic [2:0]  A, B, C
);

  // simple startup guard (no reset provided)
  logic [1:0] init_cnt = 2'd0;
  always_ff @(posedge clk) if (init_cnt != 2'd3) init_cnt <= init_cnt + 1;
  wire valid1 = (init_cnt >= 2'd1);
  wire valid2 = (init_cnt >= 2'd2);

  function automatic [7:0] dec8(input logic [2:0] v);
    dec8 = 8'b1 << (v[0] + 2*v[1] + 4*v[2]);
  endfunction

  // internal capture checks
  ap_cap_bits:  assert property (@(posedge clk) valid1 |-> {A[0],B[0],C[0]} == $past(ABC));
  ap_cap_clean: assert property (@(posedge clk) valid1 |-> (A[2:1]==2'b00 && B[2:1]==2'b00 && C[2:1]==2'b00));

  // 2-cycle latency functional mapping
  ap_decode:     assert property (@(posedge clk) valid2 && !$isunknown($past(ABC,2)) |-> Y == dec8($past(ABC,2)));
  ap_x_to_zero:  assert property (@(posedge clk) valid2 &&  $isunknown($past(ABC,2)) |-> Y == 8'b0);
  ap_onehot0:    assert property (@(posedge clk) valid2 |-> $onehot0(Y));

  // coverage: all 8 codes propagate through the 2-cycle pipeline
  genvar i;
  generate
    for (i=0; i<8; i++) begin : cg
      cp_code: cover property (@(posedge clk) valid2 && $past(ABC,2) == i && Y == (8'b1 << i));
    end
  endgenerate
endmodule

bind decoder decoder_sva u_decoder_sva(.clk(clk), .ABC(ABC), .Y(Y), .A(A), .B(B), .C(C));