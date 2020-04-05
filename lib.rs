#![cfg_attr(not(feature="std"),no_std)]
use frame_support::{
    decl_module, decl_storage, decl_event, decl_error, ensure, StorageValue, StorageMap,print,Printable,
    Parameter
};
// use rstd::convert::{Into, TryFrom, TryInto};
use sp_runtime::{traits::{ Bounded, Member}, DispatchError};
use codec::{Encode, EncodeLike, Decode, Output, Input};
use sp_arithmetic::traits::BaseArithmetic;
use system::{ensure_signed};
use sp_std::result;


use sp_std::{
    convert::{Into,From},
    prelude::*,
    result::Result,
    vec::Vec,
};
mod linkedlist;
use linkedlist::{LinkedList, LinkedItem};

/// A FRAME pallet template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references

/// For more guidance on Substrate FRAME, see the example pallet
/// https://github.com/paritytech/substrate/blob/master/frame/example/src/lib.rs


#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

/// The pallet's configuration trait.
pub trait Trait: system::Trait  {
    // Add other types and constants required to configure this pallet.
    type LogIndex: Parameter + Member + Bounded + Default+BaseArithmetic + Copy+Printable+Into<u32>;
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

}
pub struct Log(pub [u8; 16]);

#[derive(Encode,Decode,Default,Clone,PartialEq)]
pub struct LogAttr<T> where T: Trait  {
    pub senderid:Option<T::AccountId>, 
    pub ownerid:Option<T::AccountId>,
    pub info:[u8; 16],
}

impl Encode for Log {
    fn encode_to<T: Output>(&self, output: &mut T) {
        output.push(&self.0);
    }
}

impl EncodeLike for Log {}

impl Decode for Log {
    fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
        Ok(Log(Decode::decode(input)?))
    }
}

type LogLinkedItem<T> = LinkedItem<<T as Trait>::LogIndex>;
type OwnedLogList<T> = LinkedList<OwnedLogs<T>, <T as system::Trait>::AccountId, <T as Trait>::LogIndex>;

// This pallet's storage items.
decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        pub Logs get(fn logs): map hasher(blake2_128_concat) T::LogIndex => Option<Log>;
        pub LogsCount get(fn logs_count): T::LogIndex;
        pub OwnedLogs get(fn owned_logs): map hasher(blake2_128_concat) (T::AccountId, Option<T::LogIndex>) => Option<LogLinkedItem<T>>;
        LogNextId: T::LogIndex;
        /// Get kitty owner
        pub LogOwners get(fn log_owner): map hasher(blake2_128_concat) T::LogIndex => Option<T::AccountId>;
        pub LogAttrs get(fn log_attrs): map hasher(blake2_128_concat) T::LogIndex => Option<LogAttr<T>>;
        pub LogTomb get(fn log_tomb):map hasher(blake2_128_concat) T::LogIndex => Option<u32>;
        /// The storage item for our proofs.
        /// It maps a proof to the user who made the claim and when they made it.
        Proofs: map hasher(blake2_128_concat) Vec<u8> => (T::AccountId, T::BlockNumber);

    }
}

// The pallet's events
decl_event! {
    pub enum Event<T> where 
        AccountId = <T as system::Trait>::AccountId,
        LogIndex = <T as Trait>::LogIndex,
        {
        /// Event emitted when a proof has been claimed.
        ClaimCreated(AccountId, Vec<u8>),
        /// Event emitted when a claim is revoked by the owner.
        ClaimRevoked(AccountId, Vec<u8>),

        LogCreatedTransfer(AccountId,AccountId,LogIndex),

        Ask(AccountId),

        Died(AccountId, LogIndex),
    }
}
decl_error! {
    pub enum Error for Module<T: Trait> {
        /// This proof has already been claimed
        ProofAlreadyClaimed,
        /// The proof does not exist, so it cannot be revoked
        NoSuchProof,
        /// The proof is claimed by another account, so caller can't revoke it
        NotProofOwner,
        LogsCountOverflow,
    }
}

// The pallet's dispatchable functions.
decl_module! {
    /// The module declaration.
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        // Initializing errors
        // this includes information about your errors in the node's metadata.
        // it is needed only if you are using errors in your pallet
    
        // A default function for depositing events
        fn deposit_event() = default;

        /// Allow a user to claim ownership of an unclaimed proof
        fn upload_log(origin, proof: Vec<u8>) {
            // Verify that the incoming transaction is signed and store who the
            // caller of this function is.
            let sender = ensure_signed(origin)?;

            // Verify that the specified proof has not been claimed yet or error with the message
            ensure!(!Proofs::<T>::contains_key(&proof), Error::<T>::ProofAlreadyClaimed);

            // Call the `system` pallet to get the current block number
            let current_block = <system::Module<T>>::block_number();

            // Store the proof with the sender and the current block number
            Proofs::<T>::insert(&proof, (sender.clone(), current_block));

            // Emit an event that the claim was created
            Self::deposit_event(RawEvent::ClaimCreated(sender, proof));
        }

        /// Allow the owner to revoke their claim
        fn revoke_claim(origin, proof: Vec<u8>) {
            // Determine who is calling the function
            let sender = ensure_signed(origin)?;

            // Verify that the specified proof has been claimed
            ensure!(Proofs::<T>::contains_key(&proof), Error::<T>::NoSuchProof);

            // Get owner of the claim
            let (owner, _) = Proofs::<T>::get(&proof);

            // Verify that sender of the current call is the claim owner
            ensure!(sender == owner, Error::<T>::NotProofOwner);

            // Remove claim from storage
            Proofs::<T>::remove(&proof);

            // Emit an event that the claim was erased
            Self::deposit_event(RawEvent::ClaimRevoked(sender, proof));
        }
        fn create_transfer(origin,log: [u8;16],to: T::AccountId){
            let sender = ensure_signed(origin)?;
            let log_id=Self::next_log_id()?;
            let log_new=Log(log);
            Self::insert_log(&sender,log_id,log_new,log);
            Self::do_transfer(&sender, &to, log_id);
            Self::deposit_event(RawEvent::LogCreatedTransfer(sender, to, log_id));
        }
        fn ask(origin) {
            let owner = ensure_signed(origin)?;
            let mut i=None;
            let mut tmp=<OwnedLogList<T>>::read(&owner,i);
            let mut out:u32;
            while tmp.prev!=None{
                out=tmp.prev.unwrap().into();
                print(out);
                i=tmp.prev;
                tmp=<OwnedLogList<T>>::read(&owner,i);
            }
            Self::deposit_event(RawEvent::Ask(owner));

        }
        fn die(origin,log_id: <T as Trait>::LogIndex){
            let owner = ensure_signed(origin)?;
            <LogTomb<T>>::insert(log_id,1);
            Self::remove_log(&owner,log_id);
        }
    }
}
impl<T:Trait> Module<T> {
    fn next_log_id()->result::Result<T::LogIndex, DispatchError>{
        let log_id=Self::logs_count();
        if log_id==T::LogIndex::max_value(){
            return Err(Error::<T>::LogsCountOverflow.into());
        }
        Ok(log_id)
    }
    fn insert_log(owner: &T::AccountId, log_id: T::LogIndex, con: Log,l:[u8;16]){
        <Logs<T>>::insert(log_id,con);
        <OwnedLogList<T>>::append(&owner, log_id);
        <LogsCount<T>>::put(log_id+1.into());
        <LogOwners<T>>::insert(log_id,owner.clone());
        <LogAttrs<T>>::insert(log_id,LogAttr{
            senderid:Some(owner.clone()),
            ownerid:None,
            info:l,
        });
    }
    fn remove_log(owner: &T::AccountId, log_id: T::LogIndex){
        <LogOwners<T>>::remove(log_id);
        <OwnedLogList<T>>::remove(&owner, log_id);
    }
    fn do_transfer(from: &T::AccountId, to: &T::AccountId, log_id: T::LogIndex){
        <OwnedLogList<T>>::remove(&from, log_id);
        <OwnedLogList<T>>::append(&to, log_id);
        <LogOwners<T>>::insert(log_id, to);
        let inf=<LogAttrs<T>>::get(log_id).unwrap().info;
        <LogAttrs<T>>::insert(log_id,LogAttr{
            senderid:Some(from.clone()),
            ownerid:Some(to.clone()),
            info:inf.clone(),
        });
    }

}
// The pallet's errors
