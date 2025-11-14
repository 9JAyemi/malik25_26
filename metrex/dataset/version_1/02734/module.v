
module ECC_memory_block#(
    parameter n=8,
    parameter m=4
)(
    input [n-1:0] data_in,
    input we,
    output [n-1:0] data_out,
    input re
);

reg [n+m-1:0] memory_block;
reg [n-1:0] corrected_data;
reg read_enable;

function [n+m-1:0] hamming_encode;
    input [n-1:0] data;
        integer i, j, parity_pos;
        begin
            for(i=0;i<n;i=i+1)
                begin
                    hamming_encode[i+m]=data[i];
                end
            for(i=0;i<m;i=i+1)
                begin
                    parity_pos=2**i;
                    hamming_encode[parity_pos-1]=0;
                    for(j=0;j<n+m;j=j+1)
                        begin
                            if((j+1)&parity_pos)
                                begin
                                    hamming_encode[parity_pos-1]=hamming_encode[parity_pos-1]^hamming_encode[j]; 
                                end
                        end
                end
        end
endfunction

function [n-1:0] hamming_decode;
     input [n+m-1:0] encoded_data;
         integer i,j,parity_pos,error_pos;
         reg [n+m-1:0] corrected_encoded_data;
         begin
             error_pos=0;
             for(i=0;i<m;i=i+1)
                begin
                    parity_pos=2**i;
                    for(j=0;j<n+m;j=j+1)
                    begin
                        if((j+1)&parity_pos)
                            begin
                                if(encoded_data[j])
                                    begin
                                        error_pos=error_pos^(j+1);
                                    end
                            end
                    end
                end
            corrected_encoded_data=encoded_data;
            if(error_pos)
            begin
                corrected_encoded_data[error_pos-1]=~corrected_encoded_data[error_pos-1];
            end
            for(i=0;i<n;i=i+1)
                begin
                    hamming_decode[i]=corrected_encoded_data[i+m];
                end
        end
endfunction

always @(posedge we or negedge we)
    begin
        if(!we)
            begin
                memory_block<=hamming_encode(data_in);
            end
    end

always @(*)
    begin
        if(re)
        begin
            read_enable<=1'b1;
            corrected_data<=hamming_decode(memory_block);
        end
        else
            begin
                read_enable<=1'b0;
                corrected_data<=8'd0;
            end
    end

assign data_out=read_enable?corrected_data:8'd0;

endmodule