module seq_gen_sva (
    input logic       clk,
    input logic       toggle,
    input logic [3:0] counter
);

    // Counter increments when it is not at the terminal count.
    check_counter_increments_before_terminal: assert property (
        @(posedge clk) (counter != 4'd10) |=> (counter == ($past(counter) + 4'd1))
    );

    // Counter resets to zero after reaching 10.
    check_counter_resets_at_terminal: assert property (
        @(posedge clk) (counter == 4'd10) |=> (counter == 4'd0)
    );

    // Toggle stays unchanged when the counter is not 10.
    check_toggle_stable_before_terminal: assert property (
        @(posedge clk) (counter != 4'd10) |=> $stable(toggle)
    );

    // Toggle flips after the counter reaches 10.
    check_toggle_flips_at_terminal: assert property (
        @(posedge clk) (counter == 4'd10) |=> $changed(toggle)
    );

endmodule