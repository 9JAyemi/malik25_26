
module tracking_camera_system_altpll_0_dffpipe_l2c
    ( 
    input clock,
    input [0:0] d,
    output [0:0] q
    );

    reg [0:0] dffe4a;
    reg [0:0] dffe5a;
    reg [0:0] dffe6a;

    wire prn = 1'b1;
    wire sclr = 1'b0;

    always @(posedge clock) begin
        if(!prn) begin
            dffe4a <= 1;
            dffe5a <= 1;
            dffe6a <= 1;
        end
        else if(!sclr) begin
            dffe4a <= d;
            dffe5a <= dffe4a;
            dffe6a <= dffe5a;
        end
    end

    assign q = dffe6a;

endmodule