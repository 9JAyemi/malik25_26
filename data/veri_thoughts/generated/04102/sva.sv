module antares_mux_4_1_sva #(parameter WIDTH = 32) (
    input logic                  clk,
    input logic [1:0]            select,
    input logic [WIDTH-1:0]      in0,
    input logic [WIDTH-1:0]      in1,
    input logic [WIDTH-1:0]      in2,
    input logic [WIDTH-1:0]      in3,
    input logic [WIDTH-1:0]      out
);

    // select 00 routes in0 to out.
    check_select_00_routes_in0: assert property (
        @(posedge clk) (select == 2'b00) |-> (out === in0)
    );

    // select 01 routes in1 to out.
    check_select_01_routes_in1: assert property (
        @(posedge clk) (select == 2'b01) |-> (out === in1)
    );

    // select 10 routes in2 to out.
    check_select_10_routes_in2: assert property (
        @(posedge clk) (select == 2'b10) |-> (out === in2)
    );

    // select 11 routes in3 to out.
    check_select_11_routes_in3: assert property (
        @(posedge clk) (select == 2'b11) |-> (out === in3)
    );

    // With select at 00 and in0 stable, out stays stable.
    check_select_00_holds_selected_input: assert property (
        @(posedge clk) (select == 2'b00 && $stable(select) && $stable(in0)) |-> $stable(out)
    );

    // With select at 01 and in1 stable, out stays stable.
    check_select_01_holds_selected_input: assert property (
        @(posedge clk) (select == 2'b01 && $stable(select) && $stable(in1)) |-> $stable(out)
    );

    // With select at 10 and in2 stable, out stays stable.
    check_select_10_holds_selected_input: assert property (
        @(posedge clk) (select == 2'b10 && $stable(select) && $stable(in2)) |-> $stable(out)
    );

    // With select at 11 and in3 stable, out stays stable.
    check_select_11_holds_selected_input: assert property (
        @(posedge clk) (select == 2'b11 && $stable(select) && $stable(in3)) |-> $stable(out)
    );

endmodule