module my_inverter_sva (
    input logic Y,
    input logic A
);

    // Y always matches the bitwise inversion of A.
    check_output_is_inversion: assert property (
        @($global_clock) Y === ~A
    );

endmodule