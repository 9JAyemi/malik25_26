// SVA for parallel_to_serial
// Bind this file to the DUT to verify internal regs as well.
module parallel_to_serial_sva (
  input logic        clk,
  input logic [7:0]  data_in,
  input logic        serial_out,
  input logic [7:0]  shift_reg,
  input logic [2:0]  counter
);
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Counter next-state correctness
  assert property (cb disable iff (!past_valid)
    case ($past(counter))
      3'd0: counter == 3'd1;
      3'd7: counter == 3'd0;
      default: counter == $past(counter)+3'd1;
    endcase
  );

  // Counter stays within range
  assert property (cb disable iff (!past_valid)
    counter inside {[3'd0:3'd7]}
  );

  // Shift register update rules
  assert property (cb disable iff (!past_valid)
    ($past(counter)==3'd0) |-> (shift_reg == $past(data_in))
  );
  assert property (cb disable iff (!past_valid)
    ($past(counter) inside {[3'd1:3'd6]}) |-> (shift_reg == { $past(shift_reg)[6:0], 1'b0 })
  );
  assert property (cb disable iff (!past_valid)
    ($past(counter)==3'd7) |-> (shift_reg == $past(shift_reg))
  );

  // Serial output maps to the selected bit of the previous-cycle shift_reg
  assert property (cb disable iff (!past_valid)
    case ($past(counter))
      3'd0: serial_out == $past(shift_reg[7]);
      3'd1: serial_out == $past(shift_reg[6]);
      3'd2: serial_out == $past(shift_reg[5]);
      3'd3: serial_out == $past(shift_reg[4]);
      3'd4: serial_out == $past(shift_reg[3]);
      3'd5: serial_out == $past(shift_reg[2]);
      3'd6: serial_out == $past(shift_reg[1]);
      3'd7: serial_out == $past(shift_reg[0]);
    endcase
  );

  // End-to-end serialized sequence from a load event (observed at $past(counter)==0)
  // Note: first bit is from previous shift_reg[7], then data_in[6:0], then 0 due to left-shifts inserting 0s.
  assert property (cb disable iff (!past_valid)
    ($past(counter)==3'd0) |->
      (serial_out == $past(shift_reg[7])) ##1
      (serial_out == $past(data_in,1)[6]) ##1
      (serial_out == $past(data_in,2)[5]) ##1
      (serial_out == $past(data_in,3)[4]) ##1
      (serial_out == $past(data_in,4)[3]) ##1
      (serial_out == $past(data_in,5)[2]) ##1
      (serial_out == $past(data_in,6)[1]) ##1
      (serial_out == 1'b0)
  );

  // Functional coverage
  cover property (cb disable iff (!past_valid)
    ($past(counter)==3'd0) ##1 (counter==3'd1) ##1 (counter==3'd2) ##1 (counter==3'd3) ##1
    (counter==3'd4) ##1 (counter==3'd5) ##1 (counter==3'd6) ##1 (counter==3'd7) ##1 (counter==3'd0)
  );
  cover property (cb disable iff (!past_valid)
    ($past(counter)==3'd0) and (shift_reg == $past(data_in))
  );
endmodule

// Bind example:
// bind parallel_to_serial parallel_to_serial_sva u_sva(.clk(clk), .data_in(data_in), .serial_out(serial_out), .shift_reg(shift_reg), .counter(counter));