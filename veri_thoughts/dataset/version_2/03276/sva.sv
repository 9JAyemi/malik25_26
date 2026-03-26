module MUX2x1_sva #(parameter width = 8) (
    input logic             clk,
    input logic [width-1:0] out,
    input logic             sel,
    input logic [width-1:0] in0,
    input logic [width-1:0] in1
);

    // When sel is 0, out must match in0.
    check_sel_0_routes_in0: assert property (
        @(posedge clk) (sel === 1'b0) |-> (out === in0)
    );

    // When sel is 1, out must match in1.
    check_sel_1_routes_in1: assert property (
        @(posedge clk) (sel === 1'b1) |-> (out === in1)
    );

endmodule


module MUX4x1_sva #(parameter width = 8) (
    input logic             clk,
    input logic [width-1:0] out,
    input logic [1:0]       sel,
    input logic [width-1:0] in0,
    input logic [width-1:0] in1,
    input logic [width-1:0] in2,
    input logic [width-1:0] in3
);

    // When sel is 0, out must match in0.
    check_sel_0_routes_in0: assert property (
        @(posedge clk) (sel === 2'h0) |-> (out === in0)
    );

    // When sel is 1, out must match in1.
    check_sel_1_routes_in1: assert property (
        @(posedge clk) (sel === 2'h1) |-> (out === in1)
    );

    // When sel is 2, out must match in2.
    check_sel_2_routes_in2: assert property (
        @(posedge clk) (sel === 2'h2) |-> (out === in2)
    );

    // When sel is 3, out must match in3.
    check_sel_3_routes_in3: assert property (
        @(posedge clk) (sel === 2'h3) |-> (out === in3)
    );

endmodule


module MUX8x1_sva #(parameter width = 8) (
    input logic             clk,
    input logic [width-1:0] out,
    input logic [2:0]       sel,
    input logic [width-1:0] in0,
    input logic [width-1:0] in1,
    input logic [width-1:0] in2,
    input logic [width-1:0] in3,
    input logic [width-1:0] in4,
    input logic [width-1:0] in5,
    input logic [width-1:0] in6,
    input logic [width-1:0] in7
);

    // When sel is 0, out must match in0.
    check_sel_0_routes_in0: assert property (
        @(posedge clk) (sel === 3'h0) |-> (out === in0)
    );

    // When sel is 1, out must match in1.
    check_sel_1_routes_in1: assert property (
        @(posedge clk) (sel === 3'h1) |-> (out === in1)
    );

    // When sel is 2, out must match in2.
    check_sel_2_routes_in2: assert property (
        @(posedge clk) (sel === 3'h2) |-> (out === in2)
    );

    // When sel is 3, out must match in3.
    check_sel_3_routes_in3: assert property (
        @(posedge clk) (sel === 3'h3) |-> (out === in3)
    );

    // When sel is 4, out must match in4.
    check_sel_4_routes_in4: assert property (
        @(posedge clk) (sel === 3'h4) |-> (out === in4)
    );

    // When sel is 5, out must match in5.
    check_sel_5_routes_in5: assert property (
        @(posedge clk) (sel === 3'h5) |-> (out === in5)
    );

    // When sel is 6, out must match in6.
    check_sel_6_routes_in6: assert property (
        @(posedge clk) (sel === 3'h6) |-> (out === in6)
    );

    // When sel is 7, out must match in7.
    check_sel_7_routes_in7: assert property (
        @(posedge clk) (sel === 3'h7) |-> (out === in7)
    );

endmodule