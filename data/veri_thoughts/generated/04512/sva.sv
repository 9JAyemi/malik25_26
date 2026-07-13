module and8_assertions (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       clk,
    input logic [7:0] result
);

    // Result is the registered bitwise AND of the previous-cycle inputs.
    check_registered_and_value: assert property (
        @(posedge clk) disable iff ($initstate)
        result == ($past(a) & $past(b))
    );

    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_per_bit_checks
            // Each result bit is the registered AND of the matching input bits.
            check_result_bit_registered_and: assert property (
                @(posedge clk) disable iff ($initstate)
                result[i] == ($past(a[i]) & $past(b[i]))
            );
        end
    endgenerate

endmodule