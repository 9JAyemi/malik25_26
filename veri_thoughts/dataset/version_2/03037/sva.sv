module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] inputs,
    input logic up_down,
    input logic load,
    input logic [3:0] D,
    input logic [3:0] Q,
    input logic [1:0] priority_encoder_output
);

    // inputs 0001 must produce encoder output 01.
    check_encoder_map_0001: assert property (
        @(posedge clk) disable iff (reset)
        (inputs == 4'b0001) |-> (priority_encoder_output == 2'b01)
    );

    // inputs 0010 must produce encoder output 10.
    check_encoder_map_0010: assert property (
        @(posedge clk) disable iff (reset)
        (inputs == 4'b0010) |-> (priority_encoder_output == 2'b10)
    );

    // inputs 0100 must produce encoder output 11.
    check_encoder_map_0100: assert property (
        @(posedge clk) disable iff (reset)
        (inputs == 4'b0100) |-> (priority_encoder_output == 2'b11)
    );

    // All other input patterns must produce encoder output 00.
    check_encoder_default_map: assert property (
        @(posedge clk) disable iff (reset)
        !(inputs == 4'b0001 || inputs == 4'b0010 || inputs == 4'b0100) |-> (priority_encoder_output == 2'b00)
    );

    // A reset on this clock edge clears Q on the following sampled cycle.
    check_counter_reset_clears_q: assert property (
        @(posedge clk)
        reset |=> (Q == 4'b0000)
    );

    // When load is asserted out of reset, Q captures D.
    check_counter_load_captures_d: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (Q == $past(D))
    );

    // When not loading and counting up, Q increments by one.
    check_counter_counts_up: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down) |=> (Q == ($past(Q) + 4'b0001))
    );

    // When not loading and counting down, Q decrements by one.
    check_counter_counts_down: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down) |=> (Q == ($past(Q) - 4'b0001))
    );

endmodule

bind top_module top_module_sva top_module_sva_i (
    .clk(clk),
    .reset(reset),
    .inputs(inputs),
    .up_down(up_down),
    .load(load),
    .D(D),
    .Q(Q),
    .priority_encoder_output(priority_encoder_output)
);