module mux4_sva
  #(parameter width = 16)
  (
    input logic                   clk,
    input logic [width-1:0]       in0,
    input logic [width-1:0]       in1,
    input logic [width-1:0]       in2,
    input logic [width-1:0]       in3,
    input logic [1:0]             sel,
    input logic [width-1:0]       out
  );

    // Output must match the RTL's mux expression on every sampled cycle.
    check_output_matches_rtl_mux_expression: assert property (
        @(posedge clk) disable iff (1'b0)
        out === ((sel == 2'b00) ? in0 :
                 (sel == 2'b01) ? in1 :
                 (sel == 2'b10) ? in2 :
                 (sel == 2'b11) ? in3 :
                 {width{1'b0}})
    );

    // Select 00 routes input 0 to the output.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel === 2'b00) |-> (out === in0)
    );

    // Select 01 routes input 1 to the output.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel === 2'b01) |-> (out === in1)
    );

    // Select 10 routes input 2 to the output.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel === 2'b10) |-> (out === in2)
    );

    // Select 11 routes input 3 to the output.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel === 2'b11) |-> (out === in3)
    );

endmodule