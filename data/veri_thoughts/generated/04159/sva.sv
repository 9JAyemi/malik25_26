module mux_sva (
    input logic        clk,
    input logic [7:0]  in0,
    input logic [7:0]  in1,
    input logic [7:0]  in2,
    input logic [7:0]  in3,
    input logic [1:0]  sel,
    input logic        en,
    input logic [7:0]  out
);

    // The output always matches the mux function.
    check_output_matches_mux_function: assert property (
        @(posedge clk)
        out == ((sel == 2'b00) ? (en ? in0 : 8'h00) :
                (sel == 2'b01) ? (en ? in1 : 8'h00) :
                (sel == 2'b10) ? (en ? in2 : 8'h00) :
                                 (en ? in3 : 8'h00))
    );

    // When disabled, the output is zero.
    check_disabled_drives_zero: assert property (
        @(posedge clk) !en |-> (out == 8'h00)
    );

    // Select 0 routes in0 when enabled.
    check_sel0_routes_in0: assert property (
        @(posedge clk) (en && (sel == 2'b00)) |-> (out == in0)
    );

    // Select 1 routes in1 when enabled.
    check_sel1_routes_in1: assert property (
        @(posedge clk) (en && (sel == 2'b01)) |-> (out == in1)
    );

    // Select 2 routes in2 when enabled.
    check_sel2_routes_in2: assert property (
        @(posedge clk) (en && (sel == 2'b10)) |-> (out == in2)
    );

    // Select 3 routes in3 when enabled.
    check_sel3_routes_in3: assert property (
        @(posedge clk) (en && (sel == 2'b11)) |-> (out == in3)
    );

endmodule