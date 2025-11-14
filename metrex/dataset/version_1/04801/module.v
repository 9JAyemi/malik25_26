module dual_port_ram(
    // Write port
    input wrclk,
    input [7:0] di,
    input wren,
    input [5:0] wraddr,
    // Read port
    input rdclk,
    input rden,
    input [5:0] rdaddr,
    output reg [7:0] do);

     reg [7:0] ram[0:63];

    initial begin
        ram[0] = 8'b00000001;
        ram[1] = 8'b10101010;
        ram[2] = 8'b01010101;
        ram[3] = 8'b11111111;
        ram[4] = 8'b11110000;
        ram[5] = 8'b00001111;
        ram[6] = 8'b11001100;
        ram[7] = 8'b00110011;
        ram[8] = 8'b00000010;
        ram[9] = 8'b00000100;
    end

    always @ (posedge wrclk) begin
        if(wren == 1) begin
            ram[wraddr] <= di;
        end
    end

    always @ (posedge rdclk) begin
        if(rden == 1) begin
            do <= ram[rdaddr];
        end
    end

endmodule