module hc161_like_sva (
    input logic [3:0] cpu_d,
    input logic       cpu_rw,
    input logic       Ncpu_romsel,
    input logic       hc161_out0,
    input logic       hc161_out1,
    input logic       hc161_out2,
    input logic       hc161_out3
);

    // A write cycle loads all four outputs from cpu_d.
    check_write_loads_outputs: assert property (
        @(posedge Ncpu_romsel)
        (cpu_rw === 1'b0) |=> (
            {hc161_out3, hc161_out2, hc161_out1, hc161_out0} ===
            {$past(cpu_d[3]), $past(cpu_d[2]), $past(cpu_d[1]), $past(cpu_d[0])}
        )
    );

    // A non-write cycle leaves all four outputs unchanged.
    check_read_holds_outputs: assert property (
        @(posedge Ncpu_romsel)
        (cpu_rw === 1'b1) |=> (
            {hc161_out3, hc161_out2, hc161_out1, hc161_out0} ===
            {$past(hc161_out3), $past(hc161_out2), $past(hc161_out1), $past(hc161_out0)}
        )
    );

endmodule