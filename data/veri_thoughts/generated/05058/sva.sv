module ad_iobuf_sva #(
    parameter DATA_WIDTH = 1
) (
    input logic clk,
    input logic [DATA_WIDTH-1:0] dio_t,
    input logic [DATA_WIDTH-1:0] dio_i,
    input logic [DATA_WIDTH-1:0] dio_o,
    input logic [DATA_WIDTH-1:0] dio_p
);

    genvar n;
    generate
        for (n = 0; n < DATA_WIDTH; n = n + 1) begin : g_iobuf_checks
            // dio_o always matches dio_p.
            check_dio_o_matches_dio_p: assert property (
                @(posedge clk) dio_o[n] == dio_p[n]
            );

            // High dio_t makes dio_p follow dio_i.
            check_dio_p_follows_dio_i_when_dio_t_high: assert property (
                @(posedge clk) dio_t[n] |-> (dio_p[n] == dio_i[n])
            );

            // Low dio_t forces dio_p high.
            check_dio_p_forced_high_when_dio_t_low: assert property (
                @(posedge clk) !dio_t[n] |-> (dio_p[n] == 1'b1)
            );

            // High dio_t makes dio_o follow dio_i.
            check_dio_o_follows_dio_i_when_dio_t_high: assert property (
                @(posedge clk) dio_t[n] |-> (dio_o[n] == dio_i[n])
            );

            // Low dio_t forces dio_o high.
            check_dio_o_forced_high_when_dio_t_low: assert property (
                @(posedge clk) !dio_t[n] |-> (dio_o[n] == 1'b1)
            );
        end
    endgenerate

endmodule