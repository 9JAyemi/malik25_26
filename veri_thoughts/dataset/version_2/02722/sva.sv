module register_bank_sva (
  input logic clk,
  input logic [31:0] data_in,
  input logic write_en,
  input logic [4:0] read_address_1,
  input logic [4:0] read_address_2,
  input logic [31:0] read_data_1,
  input logic [31:0] read_data_2
);
  // A write captures data_in into read_data_1 on the next clock.
  check_write_capture_rd1: assert property (
    @(posedge clk) write_en |=> (read_data_1 == $past(data_in))
  );

  // A write captures data_in into read_data_2 on the next clock.
  check_write_capture_rd2: assert property (
    @(posedge clk) write_en |=> (read_data_2 == $past(data_in))
  );

  // Without a write, read_data_1 holds its value to the next clock.
  check_hold_no_write_rd1: assert property (
    @(posedge clk) !write_en |=> (read_data_1 == $past(read_data_1))
  );

  // Without a write, read_data_2 holds its value to the next clock.
  check_hold_no_write_rd2: assert property (
    @(posedge clk) !write_en |=> (read_data_2 == $past(read_data_2))
  );

  // read_data_1 only changes following a write in the previous cycle.
  check_change_requires_prev_write_rd1: assert property (
    @(posedge clk) $changed(read_data_1) |-> $past(write_en)
  );

  // read_data_2 only changes following a write in the previous cycle.
  check_change_requires_prev_write_rd2: assert property (
    @(posedge clk) $changed(read_data_2) |-> $past(write_en)
  );

  // After a write, both outputs next cycle equal that cycle's data_in.
  check_prev_write_outputs_equal_written: assert property (
    @(posedge clk) $past(write_en) |-> (read_data_1 == $past(data_in)) && (read_data_2 == $past(data_in))
  );

  // Any output change implies last cycle was a write and both outputs now equal the written data.
  check_any_change_implies_written_value: assert property (
    @(posedge clk) ($changed(read_data_1) || $changed(read_data_2)) |-> $past(write_en) && (read_data_1 == $past(data_in)) && (read_data_2 == $past(data_in))
  );

  // If outputs differ now, there was no write in the previous cycle.
  check_diff_implies_no_prev_write: assert property (
    @(posedge clk) (read_data_1 != read_data_2) |-> !$past(write_en)
  );

  // If no write this cycle and outputs are equal now, they remain equal next cycle.
  check_equal_hold_without_write: assert property (
    @(posedge clk) (!write_en && (read_data_1 == read_data_2)) |=> (read_data_1 == read_data_2)
  );
endmodule