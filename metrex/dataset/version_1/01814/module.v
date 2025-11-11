module rf_2p (
    clka    ,  
    cena_i  ,
    addra_i ,
    dataa_o ,
    clkb    ,     
    cenb_i  ,   
    wenb_i  ,   
    addrb_i ,  
    datab_i
);

parameter       Word_Width=32;
parameter       Addr_Width=8;

input                   clka;      // clock input
input                   cena_i;    // chip enable, low active
input   [Addr_Width-1:0]  addra_i;   // address input
output  [Word_Width-1:0]  dataa_o;   // data output

// B Port
input                   clkb;      // clock input                     
input                   cenb_i;    // chip enable, low active      
input                   wenb_i;    // write enable, low active        
input   [Addr_Width-1:0]  addrb_i;   // address input                   
input   [Word_Width-1:0]  datab_i;   // data input                     

reg    [Word_Width-1:0]   mem_array[(1<<Addr_Width)-1:0];

reg    [Word_Width-1:0]   dataa_r;

always @(posedge clka) begin
    if (!cena_i)
        dataa_r <= mem_array[addra_i];
    else
        dataa_r <= 'bx;
end

assign dataa_o = dataa_r;

// -- B Port --//
always @(posedge clkb) begin
    if(!cenb_i) begin
        if(wenb_i) begin
            if(datab_i > mem_array[addrb_i]) begin
                mem_array[addrb_i] <= datab_i;
            end
        end else begin
            mem_array[addrb_i] <= datab_i;
        end
    end
end

endmodule