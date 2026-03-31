module twos_complement_sva (
    input logic [3:0] a,
    input logic [3:0] twos_comp
);

    // twos_comp must equal the RTL's inverted/add-one expression.
    check_twos_comp_matches_rtl: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked2: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked3: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked4: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked5: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked6: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked7: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked8: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

    // twos_comp must equal the RTL's inverted/add-one expression with inverted[3] masked out.
    check_twos_comp_matches_rtl_masked9: assert property (
        @($global_clock)
        twos_comp == ((~a + 4'b0001) + ((~a[3]) ? 4'b0001 : 4'b0000))
    );

endmodule