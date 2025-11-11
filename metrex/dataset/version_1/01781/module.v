module counter_rollover
#(parameter       W = 256, // width of counter
  parameter       N = 4)   // how many parts contain counter?
 (input  wire         CLK,
  input  wire         ENABLE,
  input  wire         LOAD,
  input  wire [W-1:0] DI,
  output wire [W-1:0] DO
  );

reg [(W/N)-1:0] cnt [N-1:0];

wire [N-1:0] tc; // TerminalCount
wire [N-1:0] ro; // RollOver


genvar k;
generate
  for (k=0;k<N;k=k+1) begin: gen_counter

    assign tc[k] = (k==0) ? 1'b1 : (tc[k-1] && (& cnt[k-1]));
    assign ro[k] = tc[k] & ENABLE;

    always @(posedge CLK) begin
      if (LOAD)
        cnt[k] <= DI[W/N*(k+1)-1:W/N*k];
      else if (ro[k])
        cnt[k] <= cnt[k] + 1;
    end

    assign DO[W/N*(k+1)-1:W/N*k] = cnt[k];

  end
endgenerate

endmodule