module data_path_sva (
    input logic [15:0] in_data,
    input logic        in_valid,
    input logic        out_ready,
    input logic [15:0] out_data,
    input logic        out_valid,
    input logic        out_error,
    input logic        clk
);

    // Valid input with ready forwards data on the next cycle.
    check_accept_forwards_data: assert property (
        @(posedge clk) (in_valid && out_ready) |=> (out_valid && !out_error && (out_data == $past(in_data)))
    );

    // Valid input without ready raises an error on the next cycle.
    check_stall_sets_error: assert property (
        @(posedge clk) (in_valid && !out_ready) |=> (!out_valid && out_error && (out_data == 16'h0000))
    );

    // No valid input clears outputs on the next cycle.
    check_idle_clears_outputs: assert property (
        @(posedge clk) (!in_valid) |=> (!out_valid && !out_error && (out_data == 16'h0000))
    );

    // out_valid is high only for a previous-cycle valid and ready handshake.
    check_out_valid_definition: assert property (
        @(posedge clk) 1'b1 |=> (out_valid == ($past(in_valid) && $past(out_ready)))
    );

    // out_error is high only for a previous-cycle valid input without ready.
    check_out_error_definition: assert property (
        @(posedge clk) 1'b1 |=> (out_error == ($past(in_valid) && !$past(out_ready)))
    );

    // out_data matches the previous input on accept, otherwise it is zero.
    check_out_data_definition: assert property (
        @(posedge clk) 1'b1 |=> (out_data == (($past(in_valid) && $past(out_ready)) ? $past(in_data) : 16'h0000))
    );

    // out_valid and out_error are never asserted together.
    check_status_mutex: assert property (
        @(posedge clk) 1'b1 |=> !(out_valid && out_error)
    );

    // Some status bit is set iff the previous cycle had a valid input.
    check_status_tracks_in_valid: assert property (
        @(posedge clk) 1'b1 |=> ((out_valid || out_error) == $past(in_valid))
    );

endmodule