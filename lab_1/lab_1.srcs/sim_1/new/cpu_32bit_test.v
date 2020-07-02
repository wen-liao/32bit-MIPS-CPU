`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/10/2020 09:54:03 PM
// Design Name: 
// Module Name: cpu_32bit_test
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`define DELAY 20
module cpu_32bit_test();
    reg[31:0] A,B;
    reg[3:0] ALUcont;
    
    wire[31:0] result;
    wire zero;
    
    cpu_32bit f(A , B, ALUcont, result, zero);

    initial begin
    A = 32'h0; B = 32'h0; ALUcont = 3'd2;   
    #`DELAY;
    A = 32'h0; B = 32'hFFFFFFFF; ALUcont = 3'd2;   
    #`DELAY;
    A = 32'h1; B = 32'hFFFFFFFF; ALUcont = 3'd2;   
    #`DELAY;
    A = 32'hFFFFFFFF; B = 32'h1; ALUcont = 3'd2;   
    #`DELAY;
    A = 32'h0; B = 32'h0; ALUcont = 3'd6;
    #`DELAY;
    A = 32'h0; B = 32'hFFFFFFFF; ALUcont = 3'd6;
    #`DELAY;
    A = 32'h1; B = 32'h0; ALUcont = 3'd6;
    #`DELAY;
    A = 32'h100; B = 32'h0; ALUcont = 3'd6;
    #`DELAY;
    A = 32'h0; B = 32'h0; ALUcont = 3'd7;
    #`DELAY;
    A = 32'h0; B = 32'h1; ALUcont = 3'd7;
    #`DELAY;
    A = 32'h0; B = 32'hFFFFFFFF; ALUcont = 3'd7;
    #`DELAY;
    A = 32'h1; B = 32'h0; ALUcont = 3'd7;
    #`DELAY;
    A = 32'hFFFFFFFF; B = 32'h0; ALUcont = 3'd7;
    #`DELAY;
    A = 32'hFFFFFFFF; B = 32'hFFFFFFFF; ALUcont = 3'd0;
    #`DELAY;
    A = 32'hFFFFFFFF; B = 32'h12345678; ALUcont = 3'd0;
    #`DELAY;
    A = 32'h12345678; B = 32'h87654321; ALUcont = 3'd0;
    #`DELAY;
    A = 32'h0; B = 32'hFFFFFFFF; ALUcont = 3'd0;
    #`DELAY;
    A = 32'hFFFFFFFF; B = 32'hFFFFFFFF; ALUcont = 3'd1;
    #`DELAY;
    A = 32'h12345678; B = 32'h87654321; ALUcont = 3'd1;
    #`DELAY;
    A = 32'h0; B = 32'hFFFFFFFF; ALUcont = 3'd1;
    #`DELAY;
    A = 32'h0; B = 32'h0; ALUcont = 3'd1;
    #`DELAY;
    end
 
 
    initial
    begin
    $monitor("time = %2d, A =%32b, B=%32b, ALUcont=%3b, result=%32b , zero=%3b", $time, A, B, ALUcont, result, zero);
    end

endmodule
