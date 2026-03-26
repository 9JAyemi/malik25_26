module shift_register_sva #(
    parameter WIDTH = 16
) (
    input logic clk,
    input logic load,
    input logic [WIDTH-1:0] data_in,
    input logic shift,
    input logic reset,
    input logic [WIDTH-1:0] data_out
);

    // Clock is clk; reset is active-high synchronous.
    // Update priority is reset > load > shift > hold.

    // Reset clears the register to all zeros on the next cycle.
    check_reset_clears_data: assert property (
        @(posedge clk) reset |=> (data_out == {WIDTH{1'b0}})
    );

    // Load captures data_in when load is asserted without shift.
    check_load_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        (load && !shift) |=> (data_out == $past(data_in))
    );

    // Load has priority over shift when both are asserted together.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (reset)
        (load && shift) |=> (data_out == $past(data_in))
    );

    generate
        if (WIDTH > 1) begin : gen_shift_wide
            // Shift moves bits left and inserts a zero into bit 0.
            check_shift_moves_left_wide: assert property (
                @(posedge clk) disable iff (reset)
                (!load && shift) |=> (data_out == {$past(data_out[WIDTH-2:0]), 1'b0})
            );
        end else begin : gen_shift_single
            // Shift on a 1-bit register clears the only bit.
            check_shift_moves_left_single: assert property (
                @(posedge clk) disable iff (reset)
                (!load && shift) |=> (data_out == 1'b0)
            );
        end
    endgenerate

    // With no active command, the register holds its previous value.
    check_holds_value_without_commands: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !shift) |=> (data_out == $past(data_out))
    );

endmodule