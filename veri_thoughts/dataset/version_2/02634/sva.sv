module arithmetic_op_sva (
    input logic [7:0] result,
    input logic [7:0] operand1,
    input logic [7:0] operand2,
    input logic [1:0] select,
    input logic clk
);
    // Result equals the selected operation of prior-cycle operands.
    check_functional_mapping: assert property (
        @(posedge clk)
            $past(1'b1) && !$isunknown({$past(select), $past(operand1), $past(operand2)}) |-> (
                result == (
                    ($past(select) == 2'b00) ? ($past(operand1) + $past(operand2)) :
                    ($past(select) == 2'b01) ? ($past(operand1) - $past(operand2)) :
                    ($past(select) == 2'b10) ? ($past(operand1) & $past(operand2)) :
                                               ($past(operand1) | $past(operand2))
                )
            )
    );

    // Addition: next-cycle result equals sum of prior-cycle operands.
    check_add_case: assert property (
        @(posedge clk)
            $past(1'b1) && ($past(select) == 2'b00) && !$isunknown({$past(operand1), $past(operand2)}) |-> 
                (result == ($past(operand1) + $past(operand2)))
    );

    // Subtraction: next-cycle result equals difference of prior-cycle operands.
    check_sub_case: assert property (
        @(posedge clk)
            $past(1'b1) && ($past(select) == 2'b01) && !$isunknown({$past(operand1), $past(operand2)}) |-> 
                (result == ($past(operand1) - $past(operand2)))
    );

    // Bitwise AND: next-cycle result equals AND of prior-cycle operands.
    check_and_case: assert property (
        @(posedge clk)
            $past(1'b1) && ($past(select) == 2'b10) && !$isunknown({$past(operand1), $past(operand2)}) |-> 
                (result == ($past(operand1) & $past(operand2)))
    );

    // Bitwise OR: next-cycle result equals OR of prior-cycle operands.
    check_or_case: assert property (
        @(posedge clk)
            $past(1'b1) && ($past(select) == 2'b11) && !$isunknown({$past(operand1), $past(operand2)}) |-> 
                (result == ($past(operand1) | $past(operand2)))
    );

    // AND subset property: result bits are subset of both operands.
    check_and_subset: assert property (
        @(posedge clk)
            $past(1'b1) && ($past(select) == 2'b10) && !$isunknown({$past(operand1), $past(operand2)}) |-> 
                ((result & ~($past(operand1))) == 8'b0) && ((result & ~($past(operand2))) == 8'b0)
    );

    // OR superset property: result includes all 1-bits from both operands.
    check_or_superset: assert property (
        @(posedge clk)
            $past(1'b1) && ($past(select) == 2'b11) && !$isunknown({$past(operand1), $past(operand2)}) |-> 
                (((~result) & $past(operand1)) == 8'b0) && (((~result) & $past(operand2)) == 8'b0)
    );

    // When prior-cycle inputs are known, result is known in this cycle.
    check_known_result_when_inputs_known: assert property (
        @(posedge clk)
            $past(1'b1) && !$isunknown({$past(select), $past(operand1), $past(operand2)}) |-> 
                !$isunknown(result)
    );

    // If result changes across a cycle, at least one of prior-cycle inputs or select changed the cycle before.
    check_change_has_cause: assert property (
        @(posedge clk)
            $past(1'b1,2) &&
            !$isunknown({result, $past(result)}) && $changed(result) &&
            !$isunknown({$past(operand1,1), $past(operand1,2), $past(operand2,1), $past(operand2,2), $past(select,1), $past(select,2)}) |-> 
                (($past(operand1,1) != $past(operand1,2)) ||
                 ($past(operand2,1) != $past(operand2,2)) ||
                 ($past(select,1)   != $past(select,2)))
    );

    // If inputs/select are identical over the two prior cycles, result holds its value from last cycle.
    check_two_cycle_input_stability_holds_result: assert property (
        @(posedge clk)
            $past(1'b1,2) &&
            !$isunknown({$past(operand1,1), $past(operand1,2), $past(operand2,1), $past(operand2,2), $past(select,1), $past(select,2)}) &&
            ($past(operand1,1) == $past(operand1,2)) &&
            ($past(operand2,1) == $past(operand2,2)) &&
            ($past(select,1)   == $past(select,2)) |-> 
                (result == $past(result))
    );
endmodule