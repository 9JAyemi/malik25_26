module rc4(
  input clk,
  input rst_n,
  input control_in,
  input write,
  input read,
  input [7:0] keylength,
  input [7:0] keydata,
  output control_out,
  output reg [7:0] streamvalue
);

reg [7:0] state [0:255];
reg [7:0] key [0:255];
reg [7:0] i, j;
reg [7:0] keystream [0:255];
reg [7:0] plaintext [0:255];
reg [7:0] ciphertext [0:255];
reg [7:0] count;
reg [7:0] temp;

assign control_out = count == keylength;

always @(posedge clk) begin
  if (!rst_n) begin
    i <= 0;
    j <= 0;
    count <= 0;
    streamvalue <= 0;
  end else begin
    if (write) begin
      key[count] <= keydata;
      count <= count + 1;
    end
    if (control_in) begin
      if (count == keylength) begin
        for (i = 0; i < 256; i = i + 1) begin
          state[i] <= i;
          keystream[i] <= 0;
        end
        j <= 0;
        for (i = 0; i < 256; i = i + 1) begin
          j <= (j + state[i] + key[i % keylength]) & 255;
          temp <= state[i];
          state[i] <= state[j];
          state[j] <= temp;
        end
        i <= 0;
        j <= 0;
        count <= 0;
      end
    end else begin
      if (read) begin
        streamvalue <= keystream[i] ^ plaintext[i];
        i <= i + 1;
      end else begin
        plaintext[i] <= streamvalue;
        keystream[i] <= state[i];
        ciphertext[i] <= keystream[i] ^ plaintext[i];
        i <= i + 1;
        j <= (j + state[i] + key[i % keylength]) & 255;
        temp <= state[i];
        state[i] <= state[j];
        state[j] <= temp;
      end
    end
  end
end

endmodule