module mux_4_to_1_sva (
    input logic clk,
    input logic sel1,
    input logic sel2,
    input logic [3:0] d0,
    input logic [3:0] d1,
    input logic [3:0] d2,
    input logic [3:0] d3,
    input logic [3:0] out
);

// sel1=0, sel2=0 routes d0 to out.
    check_sel00_routes_d0: assert property (
        @(posedge clk) (!sel1 && !sel2) |-> (out == d0)
    );

// sel1=0, sel2=1 routes d1 to out.
    check_sel01_routes_d1: assert property (
        @(posedge clk) (!sel1 && sel2) |-> (out == d1)
    );

// sel1=1, sel2=0 routes d2 to out.
    check_sel10_routes_d2: assert property (
        @(posedge clk) (sel1 && !sel2) |-> (out == d2)
    );

// sel1=1, sel2=1 routes d3 to out.
    check_sel11_routes_d3: assert property (
        @(posedge clk) (sel1 && sel2) |-> (out == d3)
    );

endmodule
