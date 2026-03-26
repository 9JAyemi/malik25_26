module dff_keep_34 (clk, rst, d, q);
    // synthesis attribute keep_hierarchy dff_keep_34 "true";
    // synthesis attribute equivalent_register_removal dff_keep_34 "no";
    // synthesis attribute shift_extract dff_keep_34 "no";
    // synthesis attribute shreg_extract dff_keep_34 "no";
    input clk;
    input rst;
    input [33:0] d;
    output reg [33:0] q;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            q <= 34'b0;
        end
        else begin
            q <= d;
        end
    end
endmodule