

`ifndef _COMPONENTS_FF_V
`define _COMPONENTS_FF_V


module components_dff_en_rst #(
    
    parameter WIDTH = 1,
    
    parameter RESET_VAL = 0
) (
    input clk,
    input rst,
    input en,
    input [WIDTH-1:0] d,
    output [WIDTH-1:0] q
);

    reg [WIDTH-1:0] contents = RESET_VAL;

    always @ (posedge clk) begin
        if (rst == 1'b1)
            contents <= RESET_VAL;
        else if (en == 1'b1)
            contents <= d;
    end

    assign q = contents;

endmodule


module components_dff_en #(
    
    parameter WIDTH = 1
) (
    input clk,
    input en,
    input [WIDTH-1:0] d,
    output [WIDTH-1:0] q
);

    reg [WIDTH-1:0] contents;

    always @ (posedge clk) begin
        if (en == 1'b1)
            contents <= d;
    end

    assign q = contents;

endmodule


module components_dff #(
    
    parameter WIDTH = 1
) (
    input clk,
    input [WIDTH-1:0] d,
    output [WIDTH-1:0] q
);

    reg [WIDTH-1:0] contents;

    always @ (posedge clk) begin
        contents <= d;
    end

    assign q = contents;

endmodule

`endif

