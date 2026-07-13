module up_counter # ( parameter SIZE=4 )
(
    input wire              Clock,
    input wire              Reset,
    input wire              Enable,
    input wire              Load,
    input wire [SIZE-1:0]   Data,
    output reg [SIZE-1:0]   Q
);

always @ (posedge Clock or posedge Reset)
begin
    if (Reset)
        Q <= 0;
    else if (Load)
        Q <= Data;
    else if (Enable)
        Q <= Q + 1;
end

endmodule