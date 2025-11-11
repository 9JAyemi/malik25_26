// SVA for top_module and submodules. Bind these in your testbench.

module counter_sva(input clk, input reset, input [7:0] out);
  default clocking cb @(posedge clk); endclocking

  a_cnt_async_rst_now:  assert property (@(posedge reset) out==8'h00);
  a_cnt_async_rst_hold: assert property (reset |-> out==8'h00 throughout reset);

  a_cnt_inc: assert property ((!reset && !$past(reset)) |-> out == $past(out)+8'd1);

  c_cnt_wrap: cover property (!reset && !$past(reset) && $past(out)==8'hFF && out==8'h00);
endmodule

bind counter counter_sva(.clk(clk), .reset(reset), .out(out));


module register_sva(input clk, input reset, input [7:0] d, input [7:0] q);
  default clocking cb @(posedge clk); endclocking

  a_reg_async_rst_now:  assert property (@(posedge reset) q==8'h00);
  a_reg_async_rst_hold: assert property (reset |-> q==8'h00 throughout reset);

  a_reg_sample: assert property ((!reset && !$past(reset)) |-> q == $past(d));

  c_reg_sample: cover property (!reset && !$past(reset) && q != $past(q));
endmodule

bind register register_sva(.clk(clk), .reset(reset), .d(d), .q(q));


module priority_encoder_sva(input [7:0] in, input [2:0] pos);
  a_pe_i7:   assert property (@(*) in[7] |-> pos==3'b111);
  genvar i;
  generate
    for (i=6; i>=1; i=i-1) begin : gen_pe
      a_pe: assert property (@(*) (in[i] && ~(|in[7:i+1])) |-> pos == i[2:0]);
    end
  endgenerate
  a_pe_i0:   assert property (@(*) (in[0] && ~(|in[7:1])) |-> pos==3'b000);
  a_pe_zero: assert property (@(*) (~|in) |-> pos==3'b000);

  c_pe_pos_all: cover property (@(*) pos inside {3'd0,3'd1,3'd2,3'd3,3'd4,3'd5,3'd6,3'd7});
endmodule

bind priority_encoder priority_encoder_sva(.in(in), .pos(pos));


module top_module_sva; // bound into top_module
  default clocking cb @(posedge clk); endclocking

  a_pos_conn: assert property (@(*) pos == priority_encoder_out);

  a_q_async_rst_now:  assert property (@(posedge reset) q==8'h00);
  a_q_async_rst_hold: assert property (reset |-> q==8'h00 throughout reset);

  // Use ##0 to check post-NBA q; RHS comes from previous cycle
  a_q_sel_reg: assert property ((!reset && priority_encoder_out==3'b000) |-> ##0 q == $past(register_out));
  a_q_sel_cnt: assert property ((!reset && priority_encoder_out==3'b001) |-> ##0 q == $past(counter_out));
  a_q_sel_def: assert property ((!reset && !(priority_encoder_out inside {3'b000,3'b001})) |-> ##0 q == 8'h00);

  c_q_path_reg: cover property (!reset && $past(!reset) && $past(priority_encoder_out)==3'b000 && q==$past(register_out));
  c_q_path_cnt: cover property (!reset && $past(!reset) && $past(priority_encoder_out)==3'b001 && q==$past(counter_out));
  c_q_path_def: cover property (!reset && $past(!reset) && $past(priority_encoder_out) inside {3'b010,3'b011,3'b100,3'b101,3'b110,3'b111} && q==8'h00);
endmodule

bind top_module top_module_sva();