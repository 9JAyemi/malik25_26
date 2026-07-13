module mux_ff_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic       q
);

    // q starts low from the RTL initial assignment.
    check_q_initial_low: assert property (
        @(posedge clk) $initstate |-> (q == 1'b0)
    );

    // A sel value of 00 causes q to capture in[0] on the next clock.
    check_q_captures_in0: assert property (
        @(posedge clk) (sel == 2'b00) |=> (q == $past(in[0]))
    );

    // A sel value of 01 causes q to capture in[1] on the next clock.
    check_q_captures_in1: assert property (
        @(posedge clk) (sel == 2'b01) |=> (q == $past(in[1]))
    );

    // A sel value of 10 causes q to capture in[2] on the next clock.
    check_q_captures_in2: assert property (
        @(posedge clk) (sel == 2'b10) |=> (q == $past(in[2]))
    );

    // A sel value of 11 causes q to capture in[3] on the next clock.
    check_q_captures_in3: assert property (
        @(posedge clk) (sel == 2'b11) |=> (q == $past(in[3]))
    );

    // q always matches the input bit selected on the previous clock.
    check_q_matches_previous_selection: assert property (
        @(posedge clk) 1'b1 |=> (
            q == $past((sel == 2'b00) ? in[0] :
                       (sel == 2'b01) ? in[1] :
                       (sel == 2'b10) ? in[2] :
                                        in[3])
        )
    );

endmodule