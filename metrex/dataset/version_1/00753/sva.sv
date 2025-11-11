// SVA for shift_register_counter
module shift_register_counter_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        en,
  input  logic        load,
  input  logic [3:0]  data_in,
  input  logic        sel,
  input  logic [3:0]  out,
  input  logic [3:0]  shift_reg,
  input  logic [3:0]  counter
);
  // Reset clears both regs on the same clock edge
  assert property (@(posedge clk) rst |-> ##0 (shift_reg==4'h0 && counter==4'h0));

  // When disabled, both hold
  assert property (@(posedge clk) disable iff (rst)
                   (!en) |-> ##0 (shift_reg==$past(shift_reg) && counter==$past(counter)));

  // Load: shift_reg gets data_in; counter holds
  assert property (@(posedge clk) disable iff (rst)
                   (en && load) |-> ##0 (shift_reg==data_in && counter==$past(counter)));

  // Increment: counter +=1 mod-16; shift_reg holds
  assert property (@(posedge clk) disable iff (rst)
                   (en && !load) |-> ##0 (counter==($past(counter)+4'd1) && shift_reg==$past(shift_reg)));

  // Output mux correctness
  assert property (@(posedge clk) ##0 out == (sel ? counter : shift_reg));

  // Coverage
  cover property (@(posedge clk) rst ##0 (shift_reg==4'h0 && counter==4'h0));
  cover property (@(posedge clk) disable iff (rst) (en && load) ##0 (shift_reg==data_in));
  cover property (@(posedge clk) disable iff (rst) (en && !load && $past(counter)==4'hF) ##0 (counter==4'h0));
  cover property (@(posedge clk) $changed(sel));
endmodule

bind shift_register_counter shift_register_counter_sva u_shift_register_counter_sva (
  .clk(clk), .rst(rst), .en(en), .load(load), .data_in(data_in), .sel(sel),
  .out(out), .shift_reg(shift_reg), .counter(counter)
);


// SVA for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        sel,
  input  logic [3:0]  out,
  input  logic [3:0]  shift_reg_out,
  input  logic [3:0]  counter_out,
  input  logic [3:0]  sum_out
);
  // Adder correctness and top out wiring
  assert property (@(posedge clk) ##0 sum_out == ({1'b0,shift_reg_out}+{1'b0,counter_out})[3:0]);
  assert property (@(posedge clk) ##0 out == sum_out);

  // After a reset has occurred, the second instance's shift_reg is stuck at 0 => when sel==0 its out must be 0
  logic seen_reset;
  always @(posedge clk) if (rst) seen_reset <= 1'b1;
  assert property (@(posedge clk) disable iff (rst)
                   (seen_reset && (sel==1'b0)) |-> ##0 (counter_out==4'h0));

  // Coverage: see both selections and an adder overflow
  cover property (@(posedge clk) sel==1'b0);
  cover property (@(posedge clk) sel==1'b1);
  cover property (@(posedge clk) ({1'b0,shift_reg_out}+{1'b0,counter_out})[4]);
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk), .rst(rst), .sel(sel), .out(out),
  .shift_reg_out(shift_reg_out), .counter_out(counter_out), .sum_out(sum_out)
);