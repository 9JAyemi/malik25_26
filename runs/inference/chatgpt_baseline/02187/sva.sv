module data_storage_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in_data,
    input logic in_valid,
    input logic [31:0] out_data,
    input logic out_valid,
    input logic [31:0] stored_data
);
    // Reset drives storage, out_valid, and out_data to zero on the next cycle.
    reset_initializes: assert property (
        @(posedge clk) reset |=> (stored_data == 32'h0) && (out_valid == 1'b0) && (out_data == 32'h0)
    );

    // out_data continuously mirrors stored_data.
    out_data_mirrors_storage: assert property (
        @(posedge clk) out_data == stored_data
    );

    // When in_valid is 1, out_valid is 1 on the next cycle.
    out_valid_set_on_valid: assert property (
        @(posedge clk) disable iff (reset) in_valid |=> out_valid
    );

    // When in_valid is 0, out_valid is 0 on the next cycle.
    out_valid_clear_without_valid: assert property (
        @(posedge clk) disable iff (reset) !in_valid |=> !out_valid
    );

    // When in_valid is 1, stored_data captures in_data on the next cycle.
    stored_data_captures_input: assert property (
        @(posedge clk) disable iff (reset) in_valid |=> (stored_data == $past(in_data))
    );

    // When in_valid is 0, stored_data holds its previous value.
    stored_data_holds_without_valid: assert property (
        @(posedge clk) disable iff (reset) !in_valid |=> (stored_data == $past(stored_data))
    );

    // When in_valid is 0, out_data holds its previous value.
    out_data_holds_without_valid: assert property (
        @(posedge clk) disable iff (reset) !in_valid |=> (out_data == $past(out_data))
    );

    // Any change to stored_data (outside reset) must be due to prior in_valid.
    stored_data_change_requires_valid: assert property (
        @(posedge clk) disable iff (reset) $changed(stored_data) |-> $past(in_valid)
    );

    // Any change to out_data (outside reset) must be due to prior in_valid.
    out_data_change_requires_valid: assert property (
        @(posedge clk) disable iff (reset) $changed(out_data) |-> $past(in_valid)
    );

    // On in_valid, out_data reflects the in_data from the previous cycle.
    out_data_reflects_input_on_valid: assert property (
        @(posedge clk) disable iff (reset) in_valid |=> (out_data == $past(in_data))
    );
endmodule