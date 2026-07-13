module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    output logic [7:0] max
);
    // The logic is purely combinational as there are no sequential elements.

    // Comparator logic for a and b
    // ab_max should be the maximum of a and b
    comparator_ab_max: assert property (
        @(posedge clk) disable iff (!RESETn) (a > b) |-> (max == a)
    );
    comparator_ab_min: assert property (
        @(posedge clk) disable iff (!RESETn) (a <= b) |-> (max == b)
    );

    // Comparator logic for c and d
    // cd_max should be the maximum of c and d
    comparator_cd_max: assert property (
        @(posedge clk) disable iff (!RESETn) (c > d) |-> (max == c)
    );
    comparator_cd_min: assert property (
        @(posedge clk) disable iff (!RESETn) (c <= d) |-> (max == d)
    );

    // Comparator logic for ab_max and cd_max
    // abcd_max should be the maximum of ab_max and cd_max
    comparator_abcd_max: assert property (
        @(posedge clk) disable iff (!RESETn) (ab_max > cd_max) |-> (max == ab_max)
    );
    comparator_abcd_min: assert property (
        @(posedge clk) disable iff (!RESETn) (ab_max <= cd_max) |-> (max == cd_max)
    );
endmodule