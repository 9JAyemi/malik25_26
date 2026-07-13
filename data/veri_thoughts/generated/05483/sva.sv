module fourbitmuxcase_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] s,
    input logic out
);

    // Output matches the mux truth table.
    check_mux_function: assert property (
        @(posedge clk)
        out == ((s == 2'b00) ? in[0] :
                (s == 2'b01) ? in[1] :
                (s == 2'b10) ? in[2] : in[3])
    );

    // Select 00 routes in[0] to out.
    check_sel_00: assert property (
        @(posedge clk)
        (s == 2'b00) |-> (out == in[0])
    );

    // Select 01 routes in[1] to out.
    check_sel_01: assert property (
        @(posedge clk)
        (s == 2'b01) |-> (out == in[1])
    );

    // Select 10 routes in[2] to out.
    check_sel_10: assert property (
        @(posedge clk)
        (s == 2'b10) |-> (out == in[2])
    );

    // Select 11 routes in[3] to out.
    check_sel_11: assert property (
        @(posedge clk)
        (s == 2'b11) |-> (out == in[3])
    );

    // If inputs are stable, output remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk)
        ($stable(in) && $stable(s)) |-> $stable(out)
    );

endmodule