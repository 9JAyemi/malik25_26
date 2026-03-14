module shift_and_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [2:0] load_data,
    input logic [1:0] and_input,
    input logic out,
    input logic [2:0] shift_reg
);
    // Synchronous active-high reset clears shift_reg to zero in the cycle reset is 1.
    reset_clears_shift_reg: assert property (
        @(posedge clk) reset |-> (shift_reg == 3'b000)
    );

    // When load is asserted (and not reset), next cycle shift_reg equals current load_data.
    load_writes_shift_reg: assert property (
        @(posedge clk) disable iff (reset) load |=> (shift_reg == $past(load_data))
    );

    // When load is deasserted (and not reset), next cycle shift right with zero fill.
    shift_when_no_load: assert property (
        @(posedge clk) disable iff (reset) !load |=> (shift_reg == {1'b0, $past(shift_reg[2:1])})
    );

    // If shifting while shift_reg is zero, it remains zero next cycle.
    zero_sticky_when_shifting: assert property (
        @(posedge clk) disable iff (reset) (!load && (shift_reg == 3'b000)) |=> (shift_reg == 3'b000)
    );

    // With three consecutive cycles of no load, the register flushes to zero.
    flush_after_three_shifts: assert property (
        @(posedge clk) disable iff (reset) (!load)[*3] |=> (shift_reg == 3'b000)
    );

    // out equals the AND of the inputs and shift_reg[0].
    out_is_definition: assert property (
        @(posedge clk) disable iff (reset) out == (and_input[0] & and_input[1] & shift_reg[0])
    );

    // If any and_input bit is 0, out must be 0.
    out_zero_when_any_input_zero: assert property (
        @(posedge clk) disable iff (reset) ((and_input[0] == 1'b0) || (and_input[1] == 1'b0)) |-> (out == 1'b0)
    );

    // If both and_input bits are 1, out equals shift_reg[0].
    out_follows_shiftreg0_when_inputs_one: assert property (
        @(posedge clk) disable iff (reset) ((and_input[0] == 1'b1) && (and_input[1] == 1'b1)) |-> (out == shift_reg[0])
    );

    // After a load, next-cycle out uses the loaded LSB.
    out_reflects_loaded_lsb: assert property (
        @(posedge clk) disable iff (reset) load |=> (out == (and_input[0] & and_input[1] & $past(load_data[0])))
    );

    // After a shift, next-cycle out uses previous shift_reg[1].
    out_reflects_shifted_lsb: assert property (
        @(posedge clk) disable iff (reset) !load |=> (out == (and_input[0] & and_input[1] & $past(shift_reg[1])))
    );
endmodule