module arriaiigz_lvds_tx_parallel_register (
    input clk,
    input enable,
    input [3:0] datain,
    input devclrn,
    input devpor,
    output reg [3:0] dataout
);

    always @ (posedge clk) begin
        if (devpor == 1'b0 || devclrn == 1'b0) begin
            dataout <= 4'b0;
        end else if (enable == 1'b1) begin
            dataout <= datain;
        end
    end

endmodule