module sky130_fd_sc_hs__counter (
    input clk,
    input rst,
    input enable,
    input load,
    input [31:0] count_max,
    output reg [31:0] count
);

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            count <= 0;
        end else if (load) begin
            count <= count_max;
        end else if (enable) begin
            if (count == count_max) begin
                count <= 0;
            end else begin
                count <= count + 1;
            end
        end
    end

endmodule