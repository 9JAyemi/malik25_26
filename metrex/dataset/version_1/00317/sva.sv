// SVA for IrDA_transmitter
module IrDA_transmitter_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  data_in,
  input  logic [7:0]  data_reg,      // bind to DUT internal
  input  logic [3:0]  pwm_counter,   // bind to DUT internal
  input  logic        pwm_out,       // bind to DUT internal
  input  logic        ir_out
);

  function automatic logic [3:0] inc_wrap4 (input logic [3:0] x);
    return (x == 4'hF) ? 4'h0 : (x + 4'd1);
  endfunction

  // Reset drives known zeros
  assert property (@(posedge clk) rst |-> (data_reg==8'h00 && pwm_counter==4'h0 && pwm_out==1'b0));

  // Free of X/Z when not in reset
  assert property (@(posedge clk) disable iff (rst) !$isunknown({pwm_counter, data_reg[3:0], pwm_out, ir_out}));

  // Counter increments with wrap every cycle
  assert property (@(posedge clk) disable iff (rst)
    pwm_counter == inc_wrap4($past(pwm_counter))
  );

  // pwm_out is function of previous cycle's counter and data_reg[3:0]
  assert property (@(posedge clk) disable iff (rst)
    pwm_out == ($past(pwm_counter) < $past(data_reg[3:0]))
  );

  // Output matches registered PWM
  assert property (@(posedge clk) ir_out == pwm_out);

  // Coverage
  cover property (@(posedge clk) disable iff (rst) $past(pwm_counter)==4'hF && pwm_counter==4'h0); // wrap
  cover property (@(posedge clk) disable iff (rst) ($past(data_reg[3:0])==4'h0) && (pwm_out==1'b0)); // 0% duty
  cover property (@(posedge clk) disable iff (rst) ($past(data_reg[3:0])!=4'h0) && pwm_out); // some duty > 0
endmodule


// SVA for IrDA_receiver
module IrDA_receiver_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        ir_in,
  input  logic [7:0]  data_out,
  input  logic [3:0]  pwm_counter,   // bind to DUT internal
  input  logic [7:0]  data_reg       // bind to DUT internal
);

  function automatic logic [3:0] inc_wrap4 (input logic [3:0] x);
    return (x == 4'hF) ? 4'h0 : (x + 4'd1);
  endfunction

  // Reset drives known zeros
  assert property (@(posedge clk) rst |-> (data_reg==8'h00 && pwm_counter==4'h0));

  // Free of X/Z when not in reset
  assert property (@(posedge clk) disable iff (rst) !$isunknown({pwm_counter, data_reg, data_out}));

  // data_out is a pure reflection of data_reg
  assert property (@(posedge clk) data_out == data_reg);

  // While ir_in=1, counter increments (with wrap) and data_reg holds
  assert property (@(posedge clk) disable iff (rst)
    ir_in |-> (pwm_counter == inc_wrap4($past(pwm_counter)) && data_reg == $past(data_reg))
  );

  // On ir_in=0 and a nonzero pulse width, shift in MSB of the measured width and clear counter
  assert property (@(posedge clk) disable iff (rst)
    (!ir_in && $past(pwm_counter)!=4'h0)
      |-> (pwm_counter==4'h0 && data_reg=={ $past(data_reg[6:0]), $past(pwm_counter[3]) })
  );

  // On ir_in=0 with zero width, hold state
  assert property (@(posedge clk) disable iff (rst)
    (!ir_in && $past(pwm_counter)==4'h0) |-> (pwm_counter==4'h0 && data_reg==$past(data_reg))
  );

  // data_reg changes only on a valid shift event
  assert property (@(posedge clk) disable iff (rst)
    $changed(data_reg) |-> (!ir_in && $past(pwm_counter)!=4'h0)
  );

  // Coverage: observe both shifted bit values and in-band wrap
  cover property (@(posedge clk) disable iff (rst) (!ir_in && $past(pwm_counter)!=0 && $past(pwm_counter[3])==1'b0));
  cover property (@(posedge clk) disable iff (rst) (!ir_in && $past(pwm_counter)!=0 && $past(pwm_counter[3])==1'b1));
  cover property (@(posedge clk) disable iff (rst) (ir_in && $past(pwm_counter)==4'hF && pwm_counter==4'h0));
endmodule


// Example bind (connect internals explicitly)
bind IrDA_transmitter IrDA_transmitter_sva tx_sva (
  .clk(clk), .rst(rst), .data_in(data_in),
  .data_reg(data_reg), .pwm_counter(pwm_counter), .pwm_out(pwm_out),
  .ir_out(ir_out)
);

bind IrDA_receiver IrDA_receiver_sva rx_sva (
  .clk(clk), .rst(rst), .ir_in(ir_in), .data_out(data_out),
  .pwm_counter(pwm_counter), .data_reg(data_reg)
);