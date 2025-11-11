

module rng(reset, rnreset, rngbitin, rngbitinclk, rngbitoutclk, rngbitout, rngdone, handle);
input reset, rnreset, rngbitoutclk;
input rngbitin, rngbitinclk;
output rngbitout, rngdone;
output [15:0] handle;

reg [15:0] rn;
reg [3:0] bitoutcounter;



assign handle[15:0] = rn[15:0];
assign rngbitout    = rn[bitoutcounter];

assign rngdone   = (bitoutcounter == 0);
reg    initialized;

always @ (posedge rngbitoutclk or posedge reset) begin
  if (reset) begin
    bitoutcounter <= 0;
    initialized   <= 0;
  end else if (!initialized) begin
    initialized   <= 1;
    bitoutcounter <= 15;
  end else if (!rngdone) begin
    bitoutcounter <= bitoutcounter - 4'd1;
  end else begin
  end end always @ (posedge rngbitinclk or posedge rnreset) begin
  if (rnreset) begin
    rn <= 16'h0000;
  end else begin
    rn[0]  <= rngbitin ^ rn[15];
    rn[1]  <= rn[0];
    rn[2]  <= rn[1];
    rn[3]  <= rn[2];
    rn[4]  <= rn[3];
    rn[5]  <= rn[4] ^ rngbitin ^ rn[15];
    rn[6]  <= rn[5];
    rn[7]  <= rn[6];
    rn[8]  <= rn[7];
    rn[9]  <= rn[8];
    rn[10] <= rn[9];
    rn[11] <= rn[10];
    rn[12] <= rn[11] ^ rngbitin ^ rn[15];
    rn[13] <= rn[12];
    rn[14] <= rn[13];
    rn[15] <= rn[14];
  end end endmodule

