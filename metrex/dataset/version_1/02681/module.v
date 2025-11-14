module ahb_lite_memory_interface (
    input         hclk,       // AHB-Lite System Clock
    input         hresetn,    // AHB-Lite System Reset, active low
    input  [31:0] haddr,      // AHB-Lite Address bus
    input  [31:0] hwdata,     // AHB-Lite Write-data bus
    output [31:0] hrdata,     // AHB-Lite Read-data bus
    input         hwrite,     // AHB-Lite Write control signal
    input   [2:0] hsize,      // AHB-Lite Size of the transfer
    input   [1:0] htrans,     // AHB-Lite Transfer type
    input         hsel,       // AHB-Lite Slave select
    output        hready,     // AHB-Lite Transfer ready signal
    output  [1:0] hresp       // AHB-Lite Transfer response
);

    // Local parameters for AHB transfer types
    localparam IDLE  = 2'b00;
    localparam BUSY  = 2'b01;
    localparam NONSEQ = 2'b10;
    localparam SEQ   = 2'b11;

    // Memory array
    reg [31:0] memory [0:255]; // Example memory size is 256 words

    // Internal signals
    reg [31:0] internal_hrdata;
    reg        internal_hready;
    reg [1:0]  internal_hresp;

    // AHB-Lite Read/Write Logic
    always @(posedge hclk or negedge hresetn) begin
        if (!hresetn) begin
            internal_hrdata <= 32'b0;
            internal_hready <= 1'b1;
            internal_hresp <= 2'b00; // OKAY response
        end else begin
            if (hsel && htrans != IDLE && hready) begin
                if (hwrite) begin
                    // Write operation
                    memory[haddr[31:2]] <= hwdata; // Word aligned address
                end else begin
                    // Read operation
                    internal_hrdata <= memory[haddr[31:2]]; // Word aligned address
                end
                internal_hready <= 1'b1;
            end else begin
                internal_hready <= 1'b1;
            end
        end
    end

    // Output assignments
    assign hrdata = internal_hrdata;
    assign hready = internal_hready;
    assign hresp = internal_hresp;

endmodule
