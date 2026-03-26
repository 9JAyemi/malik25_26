module top_module_sva (
    input logic         clk,
    input logic         reset,
    input logic         ena,
    input logic [1023:0] in,
    input logic [7:0]   sel,
    input logic [7:0]   out,
    input logic [15:0]  counter,
    input logic [7:0]   mux_output,
    input logic [3:0]   select_input,
    input logic [11:0]  add_output
);

    // Reset clears the counter on the following cycle.
    check_reset_clears_counter: assert property (
        @(posedge clk) reset |=> (counter == 16'd0)
    );

    // Enable increments the counter by one.
    check_counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (counter == ($past(counter) + 16'd1))
    );

    // Disabled cycles hold the counter value.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !ena |=> (counter == $past(counter))
    );

    // The selector is the 4-bit shifted decode of sel[2:0].
    check_select_input_decode: assert property (
        @(posedge clk) disable iff (reset)
        (select_input == (4'b0001 << sel[2:0]))
    );

    // The mux output is always zero-extended from a 4-bit slice.
    check_mux_output_zero_extended: assert property (
        @(posedge clk) disable iff (reset)
        (mux_output[7:4] == 4'b0000)
    );

    // The mux output matches the RTL's selected input nibble.
    check_mux_output_selected_nibble: assert property (
        @(posedge clk) disable iff (reset)
        (mux_output ==
            ((sel[2:0] == 3'd0) ? {4'b0000, in[7:4]}   :
             (sel[2:0] == 3'd1) ? {4'b0000, in[11:8]}  :
             (sel[2:0] == 3'd2) ? {4'b0000, in[19:16]} :
             (sel[2:0] == 3'd3) ? {4'b0000, in[35:32]} :
                                  {4'b0000, in[3:0]}))
    );

    // The adder output is the low 12 bits of counter plus mux_output.
    check_add_output_matches_sum: assert property (
        @(posedge clk) disable iff (reset)
        (add_output == (counter[11:0] + {4'b0000, mux_output}))
    );

    // The module output is add_output[11:4].
    check_out_matches_add_output_slice: assert property (
        @(posedge clk) disable iff (reset)
        (out == add_output[11:4])
    );

    // After reset, the adder reflects a zero counter plus mux_output.
    check_reset_zeroes_counter_contribution: assert property (
        @(posedge clk) reset |=> (add_output == {4'b0000, mux_output})
    );

    // After reset, the visible output is zero.
    check_reset_forces_out_zero: assert property (
        @(posedge clk) reset |=> (out == 8'd0)
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .reset(reset),
    .ena(ena),
    .in(in),
    .sel(sel),
    .out(out),
    .counter(counter),
    .mux_output(mux_output),
    .select_input(select_input),
    .add_output(add_output)
);