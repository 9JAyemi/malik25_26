module fletcher_checksum_sva (
  input logic clk,
  input logic rst,
  input logic [7:0] data,
  input logic [15:0] sum,
  input logic [7:0] byte_count,
  input logic [15:0] sum_temp,
  input logic [15:0] sum_prev,
  input logic [15:0] sum_final,
  input logic [1:0] state
);

  ///// Reset behavior /////
  // Synchronous reset drives all registers to zero and state to 2'b00.
  reset_values: assert property (
    @(posedge clk) rst |-> (state == 2'b00) && (byte_count == 8'd0) && (sum_temp == 16'd0) &&
                    (sum_prev == 16'd0) && (sum_final == 16'd0) && (sum == 16'd0)
  );

  ///// State 2'b00 behavior /////
  // In state 2'b00, next state is 2'b01.
  state00_next_is_01: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b00) |=> (state == 2'b01)
  );
  // In state 2'b00, sum_temp adds data and byte_count increments by 1.
  state00_updates: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b00) |=> 
      (sum_temp == $past(sum_temp) + data) && (byte_count == $past(byte_count) + 8'd1)
  );

  ///// State 2'b01 behavior /////
  // In state 2'b01, sum_prev accumulates sum_temp and sum_temp clears to 0.
  state01_updates: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b01) |=> 
      (sum_prev == $past(sum_prev) + $past(sum_temp)) && (sum_temp == 16'd0)
  );
  // In state 2'b01 with byte_count == 255, next state is 2'b10.
  state01_next_when_255: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b01 && byte_count == 8'd255) |=> (state == 2'b10)
  );
  // In state 2'b01 with byte_count != 255, next state is 2'b00.
  state01_next_when_not_255: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b01 && byte_count != 8'd255) |=> (state == 2'b00)
  );

  ///// State 2'b10 behavior /////
  // In state 2'b10, sum_final updates to sum_prev % 255.
  state10_compute_final: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b10) |=> (sum_final == ($past(sum_prev) % 16'd255))
  );
  // In state 2'b10, sum updates from the previous sum_final value.
  state10_output_prev_final: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b10) |=> (sum == $past(sum_final))
  );
  // In state 2'b10, next state is 2'b11.
  state10_next_is_11: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b10) |=> (state == 2'b11)
  );

  ///// State 2'b11 behavior /////
  // In state 2'b11 with sum_final == data, next state is 2'b00.
  state11_next_when_match: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b11 && (sum_final == data)) |=> (state == 2'b00)
  );
  // In state 2'b11 with sum_final != data, state holds at 2'b11.
  state11_hold_when_mismatch: assert property (
    @(posedge clk) disable iff (rst) (state == 2'b11 && (sum_final != data)) |=> (state == 2'b11)
  );

  ///// Stability outside write states /////
  // byte_count only changes in state 2'b00.
  byte_count_stable_outside_state00: assert property (
    @(posedge clk) disable iff (rst) (state != 2'b00) |=> (byte_count == $past(byte_count))
  );
  // sum_prev only changes in state 2'b01.
  sum_prev_stable_outside_state01: assert property (
    @(posedge clk) disable iff (rst) (state != 2'b01) |=> (sum_prev == $past(sum_prev))
  );
  // sum_temp is stable in states 2'b10 and 2'b11.
  sum_temp_stable_in_10_11: assert property (
    @(posedge clk) disable iff (rst) (state inside {2'b10, 2'b11}) |=> (sum_temp == $past(sum_temp))
  );
  // sum_final only changes in state 2'b10.
  sum_final_stable_outside_state10: assert property (
    @(posedge clk) disable iff (rst) (state != 2'b10) |=> (sum_final == $past(sum_final))
  );
  // sum only changes in state 2'b10.
  sum_stable_outside_state10: assert property (
    @(posedge clk) disable iff (rst) (state != 2'b10) |=> (sum == $past(sum))
  );

endmodule