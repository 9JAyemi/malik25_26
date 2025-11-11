// SVA checkers and binds for the given DUT

// Priority encoder checker
module pe_sva_bind (input [7:0] in, input [2:0] pos);
  default clocking cb @(*); endclocking

  // Functional correctness
  assert property ( $onehot(in) |-> pos == (in[0]?3'd0:
                                            in[1]?3'd1:
                                            in[2]?3'd2:
                                            in[3]?3'd3:
                                            in[4]?3'd4:
                                            in[5]?3'd5:
                                            in[6]?3'd6:3'd7) );
  assert property ( !$onehot(in) |-> pos == 3'd0 );

  // Coverage: all one-hot cases, zero and multi-hot
  genvar i;
  generate
    for (i=0; i<8; i=i+1) begin : pe_cov
      cover property ( (in == (8'b1 << i)) && (pos == i[2:0]) );
    end
  endgenerate
  cover property ( (in == 8'b0) && (pos == 3'd0) );
  cover property ( ($countones(in) >= 2) && (pos == 3'd0) );
endmodule
bind priority_encoder pe_sva_bind pe_sva_i (.*);

// Barrel shifter mux checker
module bsm_sva_bind (input [15:0] in, input [7:0] out_hi, input [7:0] out_lo);
  default clocking cb @(*); endclocking

  // Functional correctness
  assert property ( out_hi == in[15:8] );
  assert property ( out_lo == in[7:0] );

  // Coverage: observe activity
  cover property ( $changed(in) );
  cover property ( $changed(out_hi) );
  cover property ( $changed(out_lo) );
endmodule
bind barrel_shifter_mux bsm_sva_bind bsm_sva_i (.*);

// Top-level checker
module top_sva_bind (
  input [7:0] in, input [2:0] pos,
  input [15:0] in2, input [7:0] out_hi, input [7:0] out_lo,
  input enable, input [15:0] out_sum
);
  default clocking cb @(*); endclocking

  // pos must reflect priority_encoder behavior at top output
  assert property ( $onehot(in) |-> pos == (in[0]?3'd0:
                                            in[1]?3'd1:
                                            in[2]?3'd2:
                                            in[3]?3'd3:
                                            in[4]?3'd4:
                                            in[5]?3'd5:
                                            in[6]?3'd6:3'd7) );
  assert property ( !$onehot(in) |-> pos == 3'd0 );

  // Slice pass-through at top ports
  assert property ( out_hi == in2[15:8] );
  assert property ( out_lo == in2[7:0] );

  // out_sum update on posedge enable (check after NBA using ##0)
  assert property ( @(posedge enable) ##0 out_sum == ({pos,3'b000} + {out_hi,out_lo}) );

  // out_sum can change only on a rising edge of enable
  assert property ( $changed(out_sum) |-> $rose(enable) );

  // Coverage: exercise updates with all pos values
  genvar j;
  generate
    for (j=0; j<8; j=j+1) begin : top_cov
      cover property ( @(posedge enable) pos == j[2:0] );
    end
  endgenerate
  cover property ( @(posedge enable) ({pos,3'b000} + {out_hi,out_lo} == out_sum) );
endmodule
bind top_module top_sva_bind top_sva_i (.*);