module bitwise_sva #(
    parameter int op = 0 // Mirror DUT parameter: 0=AND, 1=OR, 2=XOR, others=NOT
) (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out
);
    generate
        if (op == 0) begin : GEN_AND
            // out equals in1 AND in2.
            check_and_functional: assert property (@(posedge clk) out == (in1 & in2));
            // If out is 1 then both inputs are 1.
            check_and_out_one_implies_inputs_one: assert property (@(posedge clk) out |-> (in1 && in2));
            // If any input is 0 then out is 0.
            check_and_input_zero_implies_out_zero: assert property (@(posedge clk) (!in1 || !in2) |-> !out);
            // Commutativity holds for AND.
            check_and_commutative: assert property (@(posedge clk) out == (in2 & in1));
        end else if (op == 1) begin : GEN_OR
            // out equals in1 OR in2.
            check_or_functional: assert property (@(posedge clk) out == (in1 | in2));
            // If any input is 1 then out is 1.
            check_or_input_one_implies_out_one: assert property (@(posedge clk) (in1 || in2) |-> out);
            // If out is 0 then both inputs are 0.
            check_or_out_zero_implies_inputs_zero: assert property (@(posedge clk) !out |-> (!in1 && !in2));
            // Commutativity holds for OR.
            check_or_commutative: assert property (@(posedge clk) out == (in2 | in1));
        end else if (op == 2) begin : GEN_XOR
            // out equals in1 XOR in2.
            check_xor_functional: assert property (@(posedge clk) out == (in1 ^ in2));
            // Equal inputs produce 0.
            check_xor_equal_inputs_zero: assert property (@(posedge clk) (in1 == in2) |-> (out == 1'b0));
            // Different inputs produce 1.
            check_xor_inequal_inputs_one: assert property (@(posedge clk) (in1 != in2) |-> (out == 1'b1));
            // Commutativity holds for XOR.
            check_xor_commutative: assert property (@(posedge clk) out == (in2 ^ in1));
        end else begin : GEN_NOT
            // out equals NOT of in1 (in2 is ignored).
            check_not_functional: assert property (@(posedge clk) out == (~in1));
            // If in1 is 0 then out is 1.
            check_not_in1_zero_out_one: assert property (@(posedge clk) (in1 == 1'b0) |-> (out == 1'b1));
            // If in1 is 1 then out is 0.
            check_not_in1_one_out_zero: assert property (@(posedge clk) (in1 == 1'b1) |-> (out == 1'b0));
        end
    endgenerate
endmodule