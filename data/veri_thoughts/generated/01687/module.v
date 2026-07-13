
module verilog_module (
    input clk,
    input rst,
    input enable,
    input sampling_event,
    input test_expr,
    input prevConfigInvalid,
    output out
);

rtl_always_on_edge_wrapped rtl_aoew_t(
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .sampling_event(sampling_event),
    .test_expr(test_expr),
    .prevConfigInvalid(prevConfigInvalid),
    .out(out)
);

endmodule
module rtl_always_on_edge_wrapped (
    input clk,
    input rst,
    input enable,
    input sampling_event,
    input test_expr,
    input prevConfigInvalid,
    output reg out
);

always @(posedge clk, posedge rst) begin
    if (rst) begin
        out <= 0;
    end else if (enable) begin
        if (test_expr & ~prevConfigInvalid) begin
            out <= !out;
        end else begin
            out <= sampling_event;
        end
    end
end

endmodule