module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] out,
    input logic [1:0] det,
    input logic [3:0] q
);

    // out is a direct reflection of q.
    check_output_matches_q: assert property (
        @(posedge clk) disable iff ($initstate) out === q
    );

    // det[1] takes the previous det[0] each cycle.
    check_detector_msb_update: assert property (
        @(posedge clk) disable iff ($initstate) det[1] == $past(det[0])
    );

    // det[0] takes in[0] XOR the previous det[1].
    check_detector_lsb_update: assert property (
        @(posedge clk) disable iff ($initstate) det[0] == ($past(in[0]) ^ $past(det[1]))
    );

    // A reset cycle clears q on the following cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> q == 4'b0000
    );

    // load captures data, regardless of ena.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && load) |-> q == $past(data)
    );

    // With no reset, load, or enable, q holds its value.
    check_hold_without_load_or_enable: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && !load && !ena) |-> q == $past(q)
    );

    // With ena and no load, q shifts left and appends det[1].
    check_shift_register_update: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && !load && ena) |-> q == {$past(q[2:0]), $past(det[1])}
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .load(load),
    .ena(ena),
    .data(data),
    .out(out),
    .det(det),
    .q(q)
);