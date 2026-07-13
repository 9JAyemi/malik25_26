module top_module (
    input [7:0] binary,
    output [7:0] excess128,
    output result
);

    binary_to_excess128 binary_to_excess128_inst (
        .binary(binary),
        .excess128(excess128)
    );

    compare_binary_excess128 compare_binary_excess128_inst (
        .binary(binary),
        .excess128(excess128),
        .result(result)
    );

endmodule

module binary_to_excess128 (
    input [7:0] binary,
    output [7:0] excess128
);

    assign excess128 = binary + 128;

endmodule

module compare_binary_excess128 (
    input [7:0] binary,
    input [7:0] excess128,
    output result
);

    assign result = (binary == excess128);

endmodule