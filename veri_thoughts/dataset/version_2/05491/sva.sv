module bitwise_xor_sva (
    input logic        clk,
    input logic [7:0]  busA,
    input logic [7:0]  busB,
    input logic [7:0]  busXOR,
    input logic [7:0]  temp1,
    input logic [7:0]  temp2,
    input logic [7:0]  temp3,
    input logic [7:0]  temp4
);

    // temp1 is the bitwise XOR of the two input buses.
    check_temp1_xor: assert property (
        @(posedge clk) temp1 == (busA ^ busB)
    );

    // temp2 is the bitwise inversion of busA.
    check_temp2_invert_busA: assert property (
        @(posedge clk) temp2 == (~busA)
    );

    // temp3 is the bitwise inversion of busB.
    check_temp3_invert_busB: assert property (
        @(posedge clk) temp3 == (~busB)
    );

    // temp4 is the AND of the two inverted buses.
    check_temp4_and_stage: assert property (
        @(posedge clk) temp4 == (temp2 & temp3)
    );

    // temp4 also matches DeMorgan reduction of the inputs.
    check_temp4_demorgan: assert property (
        @(posedge clk) temp4 == (~(busA | busB))
    );

    // busXOR is the XOR of temp1 and temp4.
    check_output_final_xor: assert property (
        @(posedge clk) busXOR == (temp1 ^ temp4)
    );

    // busXOR simplifies to the bitwise NAND of the inputs.
    check_output_nand_function: assert property (
        @(posedge clk) busXOR == (~(busA & busB))
    );

    // Stable inputs keep the combinational output stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(busA) && $stable(busB)) |-> $stable(busXOR)
    );

endmodule