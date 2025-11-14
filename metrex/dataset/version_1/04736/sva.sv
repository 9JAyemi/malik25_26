// SVA for accu
// Bind these assertions to the DUT
module accu_sva(
  input               clk,
  input               rst_n,
  input       [7:0]   data_in,
  input               valid_a,
  input               ready_b,
  input               ready_a,
  input               valid_b,
  input       [9:0]   data_out,
  // internal regs
  input       [7:0]   input_reg,
  input       [3:0]   counter,
  input       [9:0]   accu_result
);
  wire accept = valid_a && ready_b;

  // Asynchronous reset effect
  assert property (@(negedge rst_n) ##0 (counter==0 && accu_result==0 && valid_b==0 && data_out==0));

  // Ready/valid relationship
  assert property (@(posedge clk) ready_a == !valid_b);

  // valid_b and counter relationship (one-cycle pulse)
  assert property (@(posedge clk) disable iff (!rst_n) (valid_b == (counter==4)));
  assert property (@(posedge clk) disable iff (!rst_n) valid_b |=> !valid_b);

  // Data-out behavior
  assert property (@(posedge clk) disable iff (!rst_n) !valid_b |-> data_out==10'd0);
  assert property (@(posedge clk) disable iff (!rst_n) valid_b |-> data_out == $past(accu_result));

  // Counter invariants and updates
  assert property (@(posedge clk) disable iff (!rst_n) counter inside {[0:4]});
  assert property (@(posedge clk) disable iff (!rst_n) (accept && counter!=4) |=> counter == $past(counter)+1);
  assert property (@(posedge clk) disable iff (!rst_n) (counter==4) |=> counter==0);

  // Accumulator updates and reset
  assert property (@(posedge clk) disable iff (!rst_n) (accept && counter!=4) |=> accu_result == $past(accu_result) + $past(data_in));
  assert property (@(posedge clk) disable iff (!rst_n) (!accept && counter!=4) |=> accu_result == $past(accu_result));
  assert property (@(posedge clk) disable iff (!rst_n) (counter==4) |=> accu_result==10'd0);

  // Input register capture behavior
  assert property (@(posedge clk) disable iff (!rst_n) accept |=> input_reg == $past(data_in));
  assert property (@(posedge clk) disable iff (!rst_n) !accept |=> input_reg == $past(input_reg));

  // Functional property: after 4 accepts (with arbitrary spacing), next cycle output is sum of the 4 inputs (mod 10 bits)
  property p_sum4_func;
    int unsigned s;
    @(posedge clk) disable iff (!rst_n)
      (s=0, 1) ##0
      ((accept, s = s + data_in) ##[0:$]
       (accept, s = s + data_in) ##[0:$]
       (accept, s = s + data_in) ##[0:$]
       (accept, s = s + data_in)) ##1
      (valid_b && data_out == s[9:0] && !ready_a);
  endproperty
  assert property (p_sum4_func);

  // Coverage
  cover property (@(posedge clk) disable iff (!rst_n)
                  (accept)[*4] ##1 valid_b); // 4 back-to-back accepts
  cover property (@(posedge clk) disable iff (!rst_n)
                  (accept ##[1:$] accept ##[1:$] accept ##[1:$] accept) ##1 valid_b); // spaced accepts
  cover property (@(posedge clk) disable iff (!rst_n)
                  (counter==3 && accept) ##1 (counter==4 && valid_b)); // output immediately after 4th accept
endmodule

// Bind to DUT (tool must allow binding to internals)
bind accu accu_sva u_accu_sva(
  .clk(clk),
  .rst_n(rst_n),
  .data_in(data_in),
  .valid_a(valid_a),
  .ready_b(ready_b),
  .ready_a(ready_a),
  .valid_b(valid_b),
  .data_out(data_out),
  .input_reg(input_reg),
  .counter(counter),
  .accu_result(accu_result)
);