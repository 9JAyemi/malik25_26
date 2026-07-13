module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    output logic [7:0] min
);
    // Combinational logic: min is assigned based on the minimum value of a, b, c, and d
    // This logic is always evaluated on the rising edge of the clock
    always_comb begin
        wire [7:0] ab_min, cd_min, abcd_min;
        ab_min = (a < b) ? a : b;
        cd_min = (c < d) ? c : d;
        abcd_min = (ab_min < cd_min) ? ab_min : cd_min;
        min = abcd_min;
    end

    // Property to check that min is correctly assigned based on the minimum value of a, b, c, and d
    // This property is always evaluated on the rising edge of the clock
    property check_min_assignment;
        @(posedge clk) disable iff (!reset_n) min == ((a < b) ? ((c < d) ? c : d) : ((a < d) ? a : d));
    endproperty

    // Assert the property to ensure that min is correctly assigned
    assert property (check_min_assignment) else $error("min is not correctly assigned");
endmodule