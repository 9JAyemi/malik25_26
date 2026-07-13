module bin_to_gray_sva (
    input logic clk,
    input logic [2:0] bin,
    input logic [2:0] gray
);
    // Mapping for bin=000 -> gray=000
    map_000: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b000)) |-> (gray == 3'b000)
    );
    // Mapping for bin=001 -> gray=001
    map_001: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b001)) |-> (gray == 3'b001)
    );
    // Mapping for bin=010 -> gray=011
    map_010: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b010)) |-> (gray == 3'b011)
    );
    // Mapping for bin=011 -> gray=010
    map_011: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b011)) |-> (gray == 3'b010)
    );
    // Mapping for bin=100 -> gray=110
    map_100: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b100)) |-> (gray == 3'b110)
    );
    // Mapping for bin=101 -> gray=111
    map_101: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b101)) |-> (gray == 3'b111)
    );
    // Mapping for bin=110 -> gray=101
    map_110: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b110)) |-> (gray == 3'b101)
    );
    // Mapping for bin=111 -> gray=100
    map_111: assert property (
        @(posedge clk) (!$isunknown(bin) && (bin == 3'b111)) |-> (gray == 3'b100)
    );
    // Unknown bin selects default mapping gray=000
    unknown_bin_drives_default_gray: assert property (
        @(posedge clk) $isunknown(bin) |-> (gray == 3'b000)
    );
    // Gray output is stable when bin input is stable
    gray_stable_when_bin_stable: assert property (
        @(posedge clk) $stable(bin) |-> $stable(gray)
    );
endmodule