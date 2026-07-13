module mux_logic_assertions (
    input logic        clk,
    input logic [2:0]  sel,
    input logic [3:0]  data0,
    input logic [3:0]  data1,
    input logic [3:0]  data2,
    input logic [3:0]  data3,
    input logic [3:0]  data4,
    input logic [3:0]  data5,
    input logic [3:0]  in1,
    input logic [3:0]  in2,
    input logic [3:0]  in3,
    input logic [3:0]  in4,
    input logic [3:0]  out_and,
    input logic [3:0]  out_or,
    input logic [3:0]  out_xor,
    input logic [3:0]  final_output,
    input logic [3:0]  mux_output
);

    // out_and is the bitwise AND of all four inputs.
    check_out_and_function: assert property (
        @(posedge clk) (out_and === (in1 & in2 & in3 & in4))
    );

    // out_or is the bitwise OR of all four inputs.
    check_out_or_function: assert property (
        @(posedge clk) (out_or === (in1 | in2 | in3 | in4))
    );

    // out_xor is the bitwise XOR of all four inputs.
    check_out_xor_function: assert property (
        @(posedge clk) (out_xor === (in1 ^ in2 ^ in3 ^ in4))
    );

    // mux_output selects data0 when sel is 000.
    check_mux_output_select_data0: assert property (
        @(posedge clk) (sel === 3'b000) |-> (mux_output === data0)
    );

    // mux_output selects data1 when sel is 001.
    check_mux_output_select_data1: assert property (
        @(posedge clk) (sel === 3'b001) |-> (mux_output === data1)
    );

    // mux_output selects data2 when sel is 010.
    check_mux_output_select_data2: assert property (
        @(posedge clk) (sel === 3'b010) |-> (mux_output === data2)
    );

    // mux_output selects data3 when sel is 011.
    check_mux_output_select_data3: assert property (
        @(posedge clk) (sel === 3'b011) |-> (mux_output === data3)
    );

    // mux_output selects data4 when sel is 100.
    check_mux_output_select_data4: assert property (
        @(posedge clk) (sel === 3'b100) |-> (mux_output === data4)
    );

    // mux_output selects data5 when sel is 101.
    check_mux_output_select_data5: assert property (
        @(posedge clk) (sel === 3'b101) |-> (mux_output === data5)
    );

    // mux_output falls back to zero for all other sel values.
    check_mux_output_default_zero: assert property (
        @(posedge clk)
        ((sel !== 3'b000) && (sel !== 3'b001) && (sel !== 3'b010) &&
         (sel !== 3'b011) && (sel !== 3'b100) && (sel !== 3'b101))
        |-> (mux_output === 4'b0000)
    );

    // final_output is data0 AND out_and when sel is 000.
    check_final_output_and_mode: assert property (
        @(posedge clk) (sel === 3'b000) |-> (final_output === (data0 & out_and))
    );

    // final_output is data1 OR out_or when sel is 001.
    check_final_output_or_mode: assert property (
        @(posedge clk) (sel === 3'b001) |-> (final_output === (data1 | out_or))
    );

    // final_output is data2 XOR out_xor when sel is 010.
    check_final_output_xor_mode: assert property (
        @(posedge clk) (sel === 3'b010) |-> (final_output === (data2 ^ out_xor))
    );

    // final_output falls back to zero for all other sel values.
    check_final_output_default_zero: assert property (
        @(posedge clk)
        ((sel !== 3'b000) && (sel !== 3'b001) && (sel !== 3'b010))
        |-> (final_output === 4'b0000)
    );

endmodule